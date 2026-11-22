from __future__ import annotations

import dataclasses
import datetime as dt
from typing import Annotated, Literal

import pytest
from pydantic import BaseModel, Field, field_validator

from celspresso import (
    CelEvaluationError,
    CelSyntaxError,
    CelTypeError,
    Env,
    Expr,
    Predicate,
    RuleSet,
    Status,
    VerificationFailed,
    function,
)
from celspresso import testing as ct


class User(BaseModel):
    age: Annotated[int, Field(ge=0, le=150)]
    roles: Annotated[list[str], Field(max_length=10)]
    tier: Literal["free", "pro"]


@pytest.fixture
def env() -> Env:
    return Env(user=User)


def U(**kw):
    base = {"age": 30, "roles": [], "tier": "free"}
    base.update(kw)
    return User(**base)


# -- compile & typing -------------------------------------------------------


def test_compile_returns_typed_exprs(env: Env) -> None:
    assert isinstance(env.compile("user.age > 3"), Predicate)
    e = env.compile("user.age + 1")
    assert isinstance(e, Expr)
    assert not isinstance(e, Predicate)
    assert e.output_type == "int"
    assert env.expr("user.age * 2", int).output_type == "int"


def test_type_errors_have_spans(env: Env) -> None:
    with pytest.raises(CelTypeError) as ei:
        env.compile("user.agee >= 18")
    assert "agee" in str(ei.value)
    assert ei.value.span[0] >= 0
    with pytest.raises(CelTypeError):
        env.predicate("user.age + 1")
    with pytest.raises(CelTypeError):
        env.expr("user.tier", int)


def test_syntax_error(env: Env) -> None:
    with pytest.raises(CelSyntaxError):
        env.compile("user.age >")


def test_decimal_rejected() -> None:
    import decimal

    with pytest.raises(TypeError, match="fixed precision"):
        Env(x=decimal.Decimal)


def test_references(env: Env) -> None:
    assert "user.age" in env.compile("user.age > 3 && user.tier == 'pro'").references


# -- evaluation -------------------------------------------------------------


def test_evaluate_model_and_dict(env: Env) -> None:
    p = env.predicate("user.age >= 18 && 'admin' in user.roles")
    assert p.evaluate({"user": U(roles=["admin"])}) is True
    assert p.evaluate({"user": {"age": 3, "roles": [], "tier": "pro"}}) is False


def test_evaluation_error_has_no_values() -> None:
    env = Env(x=int, y=int)
    with pytest.raises(CelEvaluationError) as ei:
        env.compile("x / y").evaluate({"x": 123456, "y": 0})
    assert "division by zero" in str(ei.value)
    assert "123456" not in str(ei.value)


def test_struct_result_roundtrip(env: Env) -> None:
    out = env.expr("user", User).evaluate({"user": U(age=40)})
    assert isinstance(out, User)
    assert out.age == 40


def test_explain(env: Env) -> None:
    ex = env.predicate("user.age >= 18 && user.tier == 'pro'").explain({"user": U(age=20)})
    assert ex.ok
    assert ex.value is False
    texts = dict(ex)
    assert texts["user.age >= 18"] is True
    assert texts["user.tier == 'pro'"] is False
    assert "→" in str(ex)
    assert ex.to_json()


# -- verification ---------------------------------------------------------


def test_schema_constraints_make_unsat(env: Env) -> None:
    v = env.compile("user.age > 200").satisfiable()
    assert v.status is Status.UNSAT
    assert v.unsat
    with pytest.raises(TypeError):
        bool(v)


def test_schema_constraints_can_be_disabled() -> None:
    env = Env(user=User, schema_constraints=False)
    v = env.predicate("user.age > 200").satisfiable()
    # the solver finds age=201, which Pydantic then rejects: never claim SAT on an invalid model
    assert v.unknown
    assert "validation" in (v.reason or "")

    @dataclasses.dataclass
    class Plain:
        age: Annotated[int, Field(ge=0, le=150)]

    assert Env(p=Plain, schema_constraints=False).predicate("p.age > 200").satisfiable().sat
    assert Env(p=Plain).predicate("p.age > 200").satisfiable().unsat


def test_literal_membership(env: Env) -> None:
    assert env.predicate("user.tier == 'enterprise'").satisfiable().unsat


def test_witness_is_real_and_validates(env: Env) -> None:
    p = env.predicate("user.age >= 18 && 'admin' in user.roles")
    v = p.satisfiable()
    assert v.sat
    assert v.witness is not None
    py = v.witness.to_python()
    assert isinstance(py["user"], User)
    assert p.evaluate(py) is True


def test_always_true_and_counterexample(env: Env) -> None:
    assert env.predicate("user.age >= 0").always_true().proved
    v = env.predicate("user.age >= 18").always_true()
    assert v.refuted
    assert v.counterexample is not None
    assert v.counterexample["user"]["age"] < 18
    with pytest.raises(VerificationFailed, match="counterexample"):
        v.expect()


def test_implies(env: Env) -> None:
    a = env.predicate("user.age >= 21")
    assert a.implies("user.age >= 18").proved
    assert env.predicate("user.age >= 18").implies(a).refuted


def test_equivalence_strict_vs_as_false() -> None:
    env = Env(x=int, y=int)
    a = env.predicate("y != 0 && x / y > 1")
    b = env.predicate("x / y > 1 && y != 0")
    # && absorbs errors commutatively in CEL, so these really are equal
    assert a.equivalent(b).proved
    c = env.predicate("x / y > 1")
    assert a.equivalent(c).refuted  # c errors on y == 0, a is false
    assert a.equivalent(c, errors="as_false").proved


def test_int_semantics() -> None:
    env = Env(x=int)
    # CEL truncates toward zero: -7 / 2 == -3
    assert env.predicate("x == -7 && x / 2 == -3").satisfiable().sat
    assert env.predicate("x == -7 && x / 2 == -4").satisfiable().unsat
    assert env.compile("x + 1").can_error().sat  # overflow at int64 max


def test_can_error_and_assumptions() -> None:
    env = Env(x=int, y=int)
    e = env.compile("x / y")
    assert e.can_error().sat
    assert e.can_error(assuming="y != 0 && y != -1").unsat


def test_vacuous_assumptions_unknown(env: Env) -> None:
    v = env.predicate("user.age > 3").always_true(assuming=["user.age < 0"])
    assert v.unknown
    assert v.reason
    assert "assumption" in v.reason


def test_env_level_assumptions(env: Env) -> None:
    adults = env.extend(assumptions=["user.age >= 18"])
    assert adults.predicate("user.age >= 18").always_true().proved
    assert adults.assumptions == ("user.age >= 18",)


def test_combinators(env: Env) -> None:
    a = env.predicate("user.age >= 18")
    b = env.predicate("user.tier == 'pro'")
    c = a & ~b | "user.age > 100"
    assert isinstance(c, Predicate)
    assert c.evaluate({"user": U(age=20, tier="free")}) is True
    assert (a & ~a).satisfiable().unsat
    limit = env.expr("user.tier == 'pro' ? 1000 : 10", int)
    assert limit.gt(500).equivalent(b).proved
    assert limit.can_equal(10).sat
    assert limit.can_equal(11).unsat
    assert a != b  # == is syntactic identity, never a CEL comparison
    with pytest.raises(TypeError):
        bool(a)


def test_mixed_env_rejected(env: Env) -> None:
    other = Env(x=int)
    with pytest.raises(ValueError, match="different environments"):
        env.predicate("user.age > 1") & other.predicate("x > 1")


def test_model_validation_downgrades_to_unknown() -> None:
    class Odd(BaseModel):
        n: int

        @field_validator("n")
        @classmethod
        def odd(cls, v: int) -> int:
            if v % 2 == 0:
                raise ValueError("even")
            return v

    env = Env(o=Odd)
    v = env.predicate("o.n == 4").satisfiable()
    assert v.unknown
    assert "validation" in (v.reason or "")


# -- strings, lists, nullable, dates, dataclasses --------------------------


def test_strings_and_regex() -> None:
    env = Env(s=Annotated[str, Field(max_length=8)])
    assert env.predicate("s.startsWith('ab') && s.endsWith('yz') && size(s) == 4").satisfiable().sat
    assert env.predicate("s.matches('^[0-9]+$') && s.contains('x')").satisfiable().unsat
    assert env.predicate("size(s) > 8").satisfiable().unsat


def test_lists_bounded_by_max_length(env: Env) -> None:
    v = env.predicate("user.roles.all(r, r == 'a') && size(user.roles) > 10").satisfiable()
    assert v.unsat
    assert not v.bounded
    unbounded = Env(xs=list[int])
    w = unbounded.predicate("xs.all(x, x > 0)").implies("xs.exists(x, x > 0) || size(xs) == 0")
    assert w.unknown
    assert w.bounded
    assert "max_length" in (w.reason or "")
    # SAT witnesses are always real, even for unbounded lists
    assert unbounded.predicate("xs.exists(x, x > 5)").satisfiable().sat
    bounded = Env(xs=Annotated[list[int], Field(max_length=4)])
    assert bounded.predicate("xs.all(x, x > 0)").implies("xs.exists(x, x > 0) || size(xs) == 0").proved


def test_nullable() -> None:
    class P(BaseModel):
        nick: str | None = None

    env = Env(p=P)
    assert env.predicate("p.nick == null").satisfiable().sat
    assert env.predicate("p.nick != null && p.nick == 'bo'").satisfiable().sat
    assert env.predicate("p.nick == null").evaluate({"p": P()}) is True


def test_dates() -> None:
    env = Env(dob=dt.date, today=dt.date)
    p = env.predicate("dob.ageOn(today) >= 18")
    assert p.evaluate({"dob": dt.date(2000, 1, 1), "today": dt.date(2020, 1, 1)}) is True
    assert p.evaluate({"dob": dt.date(2002, 6, 1), "today": dt.date(2020, 1, 1)}) is False
    v = (p & env.predicate("today == date('2026-01-01')")).satisfiable()
    assert v.sat
    w = v.witness.to_python()
    assert isinstance(w["dob"], dt.date)
    assert w["dob"] <= dt.date(2008, 1, 1)


def test_dataclass_schema() -> None:
    @dataclasses.dataclass
    class Point:
        x: int
        y: int

    env = Env(p=Point)
    assert env.predicate("p.x > p.y").evaluate({"p": Point(2, 1)}) is True
    v = env.predicate("p.x > p.y && p.y > 5").satisfiable()
    assert isinstance(v.witness.to_python()["p"], Point)


# -- definitions, tables, functions ----------------------------------------


def test_define_and_table(env: Env) -> None:
    e = env.define("adult", "user.age >= 18").table("staff_roles", {"admin", "ops"})
    p = e.predicate("adult && user.roles.exists(r, r in staff_roles)")
    assert p.evaluate({"user": U(age=40, roles=["ops"])}) is True
    assert p.implies("user.age >= 18").proved
    assert "adult" not in p.canonical


# -- RuleSet, diff, testing helpers ----------------------------------------


def test_ruleset(env: Env) -> None:
    rs = RuleSet(
        {
            "minor": env.predicate("user.age < 18"),
            "adult": env.predicate("user.age >= 18"),
            "dead": env.predicate("user.age > 500"),
        }
    )
    assert set(rs.unreachable()) == {"dead"}
    overlaps = rs.check_pairwise(lambda a, b: (a & b).satisfiable())
    assert overlaps[("minor", "adult")].unsat
    assert rs.evaluate({"user": U(age=3)}) == {"minor": True, "adult": False, "dead": False}


def test_diff(env: Env) -> None:
    old = env.predicate("user.age >= 18")
    new = env.predicate("user.age >= 21")
    ws = old.diff(new, limit=3)
    assert 1 <= len(ws) <= 3
    ages = {w["user"]["age"] for w in ws}
    assert all(18 <= a < 21 for a in ages)
    assert len(ages) == len(ws)


def test_testing_helpers(env: Env) -> None:
    ct.assert_implies(env.predicate("user.age > 30"), "user.age > 20")
    ct.assert_never(env.predicate("user.age < 0"))
    ct.assert_no_errors(env.compile("user.age + 1"))
    with pytest.raises(AssertionError):
        ct.assert_equivalent(env.predicate("user.age > 1"), "user.age > 2")


def test_custom_function_cannot_shadow_builtin_overload() -> None:
    @function
    def double(n: int) -> int:  # CEL already has double(int) -> double
        return n

    with pytest.raises(ValueError, match="clashes with existing overload"):
        Env(n=int).extend(functions=[double])

    @function(name="size")
    def size_of_int(n: int) -> int:  # a new overload of an existing name is fine
        return n

    assert Env(n=int).extend(functions=[size_of_int]).compile("size(n)").evaluate({"n": 4}) == 4


# -- inputs are held to the schema the proofs assume -------------------------


def test_evaluate_enforces_schema_constraints() -> None:
    class M(BaseModel):
        x: Annotated[int, Field(le=10)]
        tags: Annotated[list[Annotated[str, Field(max_length=3)]], Field(max_length=2)] = []

    env = Env(m=M)
    p = env.predicate("m.x <= 10")
    assert p.always_true().proved
    assert p.evaluate({"m": {"x": 10, "tags": []}}) is True
    # a dict (or a mutated model) that breaks a constraint the proof relied on is rejected,
    # naming the path and the constraint but never the value
    with pytest.raises(ValueError, match=r"input 'm.x' violates the schema: must be <= 10") as exc:
        p.evaluate({"m": {"x": 99, "tags": []}})
    assert "99" not in str(exc.value)
    m = M(x=1)
    m.x = 99
    with pytest.raises(ValueError, match=r"m\.x"):
        p.evaluate({"m": m})
    with pytest.raises(ValueError, match=r"'m.tags\[1\]' violates the schema: length must be <= 3"):
        p.evaluate({"m": {"x": 1, "tags": ["ok", "toolong"]}})
    with pytest.raises(ValueError, match="must be one of"):
        Env(t=Literal["a", "b"]).predicate("t == 'a'").explain({"t": "c"})


def test_limits_cap_evaluation_cost() -> None:
    from celspresso import Limits

    env = Env(xs=list[int], limits=Limits(max_iterations=10))
    p = env.predicate("xs.all(x, x > 0)")
    assert p.evaluate({"xs": [1, 2, 3]}) is True
    with pytest.raises(CelEvaluationError, match="iteration limit"):
        p.evaluate({"xs": list(range(1, 100))})
    # limits survive extending the env
    wider = env.extend(assumptions=["size(xs) >= 0"])
    with pytest.raises(CelEvaluationError, match="iteration limit"):
        wider.predicate("xs.all(x, x > 0)").evaluate({"xs": list(range(1, 100))})
    with pytest.raises(ValueError, match="positive int"):
        Limits(max_cost=0)
    with pytest.raises(TypeError, match="limits"):
        Env(x=int, limits=5)  # type: ignore[arg-type]


# -- honest semantics: null fields, dyn values, runtime failures ----------------


def test_has_is_false_for_null_fields() -> None:
    class Ticket(BaseModel):
        note: str | None = None

    env = Env(o=Ticket)
    guarded = env.predicate("has(o.note) && o.note.startsWith('x')")
    assert env.predicate("has(o.note)").evaluate({"o": {"note": None}}) is False
    assert guarded.evaluate({"o": {"note": None}}) is False
    assert guarded.evaluate({"o": {"note": "xy"}}) is True
    # the prover agrees with the evaluator: the guard really guards
    assert guarded.can_error().unsat
    assert env.predicate("has(o.note) == (o.note != null)").always_true().proved
    assert env.predicate("o.note.startsWith('x')").can_error().sat


def test_dyn_values_get_an_honest_reason() -> None:
    from typing import Any

    class Call(BaseModel):
        args: dict[str, Any]

    env = Env(call=Call)
    p = env.predicate("call.args.amount > 5")
    assert p.evaluate({"call": {"args": {"amount": 9}}}) is True
    v = p.satisfiable()
    assert v.unknown
    assert v.reason is not None
    assert "dyn" in v.reason
    assert "concrete type" in v.reason
    assert "_>_" not in v.reason
    assert not v.bounded
    assert "unroll" not in str(v)


def test_check_rule_names_the_runtime_failure() -> None:
    env = Env(n=Annotated[int, Field(ge=0, le=10)])
    r = env.check_rule("100 / n > 1000 / 0")
    assert [p.kind for p in r.problems] == ["never_fires"]
    assert "evaluation fails (division by zero)" in str(r)
    r = env.check_rule("100 / n > 1")
    assert [p.kind for p in r.problems] == ["can_error"]
    assert "evaluation fails (division by zero) when n = 0" in str(r)
