"""Edge cases of the public surface: type mapping, literals, errors, reprs, RuleSet."""

from __future__ import annotations

import dataclasses
import datetime as dt
import enum
from typing import Annotated, Literal

import pytest
from pydantic import BaseModel, Field

from celspresso import (
    CelEvaluationError,
    CelTypeError,
    Env,
    Predicate,
    RuleSet,
    Status,
    Verdict,
    VerificationFailed,
    VerificationTimeout,
    function,
)
from celspresso import testing as ct
from celspresso._types import cel_literal, type_name

# -- type mapping ----------------------------------------------------------


class Color(enum.Enum):
    RED = "red"
    BLUE = "blue"


class Level(enum.IntEnum):
    LOW = 1
    HIGH = 3


def test_enum_and_literal_membership() -> None:
    env = Env(c=Color, lv=Level, n=Literal[1, 2], flag=Literal[True])
    assert env.variables == {"c": "string", "lv": "int", "n": "int", "flag": "bool"}
    assert env.predicate("c == 'green'").satisfiable().refuted
    assert env.predicate("lv == 2").satisfiable().refuted
    assert env.predicate("n == 2").satisfiable().proved
    assert env.predicate("n == 3").satisfiable().refuted


@pytest.mark.parametrize(
    ("tp", "name"),
    [
        (tuple[int, ...], "list(int)"),
        (tuple[str, str], "list(string)"),
        (set[int], "list(int)"),
        (frozenset[str], "list(string)"),
        (list, "list(dyn)"),
        (dict, "map(dyn, dyn)"),
        (dict[str, int], "map(string, int)"),
        (int | None, "int?"),
        (float, "double"),
        (bytes, "bytes"),
        ("uint", "uint"),
    ],
)
def test_type_names(tp: object, name: str) -> None:
    assert Env(v=tp).variables["v"] == name


@pytest.mark.parametrize(
    ("tp", "match"),
    [
        (int | str, "Optional"),
        (tuple[int, str], "heterogeneous"),
        (Literal["a", 1], "Literal"),
        (complex, "cannot map"),
    ],
)
def test_unsupported_types(tp: object, match: str) -> None:
    with pytest.raises(TypeError, match=match):
        Env(v=tp)


def test_mixed_enum_rejected() -> None:
    class Mixed(enum.Enum):
        A = "a"
        B = 1

    with pytest.raises(TypeError, match="all-str or all-int"):
        Env(m=Mixed)


def test_nested_models_and_name_collisions() -> None:
    class Addr(BaseModel):
        zip: Annotated[str, Field(min_length=5, max_length=5, pattern=r"^[0-9]+$")]

    class Person(BaseModel):
        addr: Addr
        tags: dict[str, int] = {}

    def make() -> type:
        class Addr(BaseModel):  # same name, different class
            line: str

        return Addr

    env = Env(p=Person, other=make())
    assert env.variables["other"] != "Addr"
    assert env.predicate("p.addr.zip == '1234'").satisfiable().refuted
    assert env.predicate("p.addr.zip.startsWith('9')").satisfiable().proved
    out = env.expr("p", Person).evaluate(
        {"p": Person(addr=Addr(zip="12345"), tags={"a": 1}), "other": {"line": "x"}}
    )
    assert isinstance(out.addr, Addr)


def test_classes_sharing_module_and_qualname_stay_distinct() -> None:
    # Django's migration models all live in one fake module, with the same qualnames
    def model(field: str) -> type:
        cls = dataclasses.make_dataclass("Order", [(field, int)])
        cls.__module__ = "__fake__"
        return cls

    a, b, c = model("a"), model("b"), model("c")
    env = Env(x=a, y=b, z=c, again=c)
    assert len({env.variables[v] for v in ("x", "y", "z")}) == 3
    assert env.variables["again"] == env.variables["z"]
    assert env.predicate("x.a + y.b + z.c + again.c > 0").evaluate(
        {"x": a(a=1), "y": b(b=1), "z": c(c=1), "again": c(c=1)}
    )
    w = env.predicate("z.c > 5").satisfiable().witness
    assert w is not None
    z = w.to_python()["z"]
    assert type(z) is c
    assert z.c > 5


def test_string_annotations_resolve_in_their_own_module(tmp_path, monkeypatch) -> None:
    (tmp_path / "shop_a.py").write_text(
        "from dataclasses import dataclass\n@dataclass\nclass Order:\n    a: int\n"
    )
    (tmp_path / "shop_b.py").write_text(
        "from __future__ import annotations\nfrom dataclasses import dataclass\n"
        "@dataclass\nclass Order:\n    b: int\n@dataclass\nclass Holder:\n    o: Order\n"
    )
    monkeypatch.syspath_prepend(str(tmp_path))
    import shop_a  # type: ignore[import-not-found]
    import shop_b  # type: ignore[import-not-found]

    env = Env(x=shop_a.Order, h=shop_b.Holder)  # shop_a.Order must not hide shop_b's
    assert env.predicate("h.o.b > 0 && x.a > 0").satisfiable().proved


def test_envs_over_different_same_named_structs_are_different() -> None:
    def model(field: str) -> type:
        cls = dataclasses.make_dataclass("Order", [(field, int)])
        cls.__module__ = "__fake__"
        return cls

    e1, e2 = Env(x=model("a")), Env(x=model("b"))
    p1, p2 = e1.predicate("x.a > 0"), e2.predicate("x.b > 0")
    with pytest.raises(ValueError, match="different environments"):
        p1 & p2
    with pytest.raises(ValueError, match="different environments"):
        p1.implies(p2)


def test_type_name_helper() -> None:
    assert type_name(("map", "string", ("list", "int"))) == "map(string, list(int))"
    assert type_name(("nullable", ("struct", "User"))) == "User?"


@pytest.mark.parametrize(
    ("value", "src"),
    [
        (None, "null"),
        (True, "true"),
        (False, "false"),
        (Color.RED, '"red"'),
        (2**63, "9223372036854775808u"),
        (1.0, "1.0"),
        (1e100, "1e+100"),
        ('a"b\\\n', '"a\\"b\\\\\\n"'),
        (b"hi", 'b"hi"'),
        (dt.date(2024, 2, 29), 'date("2024-02-29")'),
        ([1, 2], "[1, 2]"),
        ({2, 1}, "[1, 2]"),
        ({"k": [1]}, '{"k": [1]}'),
    ],
)
def test_cel_literal(value: object, src: str) -> None:
    assert cel_literal(value) == src


def test_cel_literal_rejects() -> None:
    with pytest.raises(TypeError, match="datetime"):
        cel_literal(dt.datetime(2024, 1, 1))
    with pytest.raises(TypeError):
        cel_literal(object())


# -- env construction -------------------------------------------------------


def test_env_construction_errors() -> None:
    env = Env(x=int)
    with pytest.raises(ValueError, match="already declared"):
        env.extend(x=str)
    with pytest.raises(ValueError, match="invalid definition"):
        env.define("not a name", "x")
    with pytest.raises(CelTypeError):
        env.define("bad", "x + 'a'")
    with pytest.raises(CelTypeError):
        env.assume("x + 1")

    def nohint(a):  # type: ignore[no-untyped-def]
        return a

    def noreturn(a: int):  # type: ignore[no-untyped-def]
        return a

    with pytest.raises(TypeError, match="type hint"):
        env.extend(functions=[nohint])
    with pytest.raises(TypeError, match="return type"):
        env.extend(functions=[noreturn])


def test_env_introspection_and_options() -> None:
    env = Env(x=int, s=str).extend(timeout=1.0, unroll_limit=2, y=int)
    assert repr(env) == "Env(x: int, s: string, y: int)"
    assert env._timeout == 1.0
    assert env._unroll == 2


def test_renamed_function_and_table_mapping() -> None:
    @function(name="double_it")
    def dbl(n: int) -> int:
        return n * 2

    env = Env(n=int, code=str).extend(functions=[dbl]).table("price", {"a": 10, "b": 20})
    assert env.compile("double_it(n) + price[code]").evaluate({"n": 2, "code": "b"}) == 24
    with pytest.raises(CelEvaluationError):
        env.compile("price[code]").evaluate({"n": 0, "code": "zzz"})


def test_function_that_raises_is_an_evaluation_error() -> None:
    @function
    def boom(n: int) -> int:
        raise RuntimeError("secret 42")

    env = Env(n=int).extend(functions=[boom])
    with pytest.raises(CelEvaluationError) as ei:
        env.compile("boom(n)").evaluate({"n": 1})
    assert "secret" not in str(ei.value)


def test_expr_type_assertions() -> None:
    env = Env(x=int, d=dict)
    p = env.expr("x > 1", bool)
    assert isinstance(p, Predicate)
    with pytest.raises(CelTypeError, match="unknown type"):  # dyn values are outside the subset
        env.expr("d['k']", int)


# -- expressions ------------------------------------------------------------


def test_expr_equality_is_syntactic_and_hashable() -> None:
    env = Env(x=int)
    a, b = env.predicate("x > 1"), env.predicate("x>1")
    c = env.predicate("1 < x")
    assert a == b
    assert a != c  # same meaning, different text: use .equivalent()
    assert a.equivalent(c).proved
    assert a != "x > 1"
    assert {a, b, c} == {a, c}
    assert {a: "rule"}[b] == "rule"
    assert env.compile("x") != Env(x=int, y=int).compile("x")  # different envs


def test_option_names_as_variables() -> None:
    env = Env({"timeout": int, "unroll_limit": str}, timeout=2.0, flag=bool)
    assert env.variables == {"timeout": "int", "unroll_limit": "string", "flag": "bool"}
    assert env.predicate("timeout > 3 && flag").evaluate({"timeout": 5, "unroll_limit": "", "flag": True})
    env2 = Env(x=int).extend({"functions": list[int], "assumptions": str}, unroll_limit=3)
    assert env2.variables["functions"] == "list(int)"
    assert env2.predicate("size(functions) > 0").satisfiable().proved


@pytest.mark.parametrize(
    "kwargs",
    [{"timeout": int}, {"timeout": True}, {"unroll_limit": 2.5}],
)
def test_option_clash_gives_clear_error(kwargs: dict[str, object]) -> None:
    with pytest.raises(TypeError, match="is an Env option"):
        Env(**kwargs)  # type: ignore[arg-type]


def test_extend_option_clashes() -> None:
    env = Env(x=int)
    with pytest.raises(TypeError, match="is an Env option"):
        env.extend(functions=int)  # type: ignore[arg-type]
    with pytest.raises(TypeError, match=r"env\.assume"):
        env.extend(assumptions=["x > 0"])
    with pytest.raises(TypeError, match="plain callables"):
        env.extend(functions=[int])
    with pytest.raises(ValueError, match="both in the mapping"):
        Env({"x": int}, x=str)
    with pytest.raises(ValueError, match="invalid variable name"):
        Env({"not valid": int})
    assert env.assume("x > 0").assume(env.predicate("x < 9")).assumptions == ("x > 0", "x < 9")
    with pytest.raises(TypeError, match="CEL conditions"):
        env.assume(5)  # type: ignore[arg-type]
    with pytest.raises(ValueError, match="different Env"):
        env.assume(Env(y=int).predicate("y > 0"))


def test_expr_identity_and_repr() -> None:
    env = Env(x=int)
    a, b = env.compile("x + 1"), env.compile("x+1")
    assert a.same_as(b)
    assert hash(a) == hash(b)
    assert repr(a) == "Expr('x + 1', type=int)"
    assert a.env is env


def test_all_comparison_builders() -> None:
    env = Env(x=int, y=int)
    x, y = env.compile("x"), env.compile("y")
    data = {"x": 1, "y": 2}
    assert x.ne(y).evaluate(data) is True
    assert x.lt(y).evaluate(data) is True
    assert x.le(1).evaluate(data) is True
    assert x.gt(0).evaluate(data) is True
    assert x.ge(y).evaluate(data) is False
    assert x.in_([1, 2]).evaluate(data) is True
    assert x.lt(y).equivalent(y.gt(x)).proved


def test_as_false_requires_predicates() -> None:
    env = Env(x=int)
    with pytest.raises(TypeError, match="predicates"):
        env.compile("x + 1").equivalent("x + 1", errors="as_false")


def test_diff_with_no_differences_and_flat_vars() -> None:
    env = Env(x=int)
    assert env.predicate("x > 1").diff(env.predicate("1 < x")) == []
    ds = env.predicate("x > 1").diff(env.predicate("x > 3"), limit=5)
    # x=2 and x=3 differ for the same reason (x > 1 holds, x > 3 doesn't): one class
    assert [d.witness["x"] in (2, 3) for d in ds] == [True]
    assert str(ds[0]) == f"when x = {ds[0].witness['x']}: true -> false"
    errs = env.compile("10 / x").diff(env.compile("10"), limit=1, assuming="x == 0")
    assert isinstance(errs[0].before, CelEvaluationError)
    assert str(errs[0]).endswith(": error (division by zero) -> 10")


def test_diff_witnesses_respect_assumptions() -> None:
    env = Env(x=int, y=int)
    old, new = env.predicate("x > 1"), env.predicate("x > 1 || y > 5")
    ds = old.diff(new, limit=5, assuming="y == 777")
    assert ds
    assert all(d.witness["y"] == 777 for d in ds)
    assert old.diff(new, assuming=[env.predicate("y <= 5")]) == []
    rs_old = RuleSet({"r": old}, assumptions=["y == 9"])
    assert [d.witness["y"] for d in rs_old.diff(RuleSet({"r": new}))["r"]] == [9]


def test_explain_error_and_nesting() -> None:
    env = Env(x=int, y=int)
    ex = env.compile("x > 0 && x / y > 1").explain({"x": 1, "y": 0})
    assert not ex.ok
    assert "division by zero" in str(ex.value)
    rendered = str(ex)
    assert "error:" in rendered
    assert "  " in rendered  # children are indented
    assert repr(ex).startswith("Explanation(ok=False")
    assert any("error" in node for node in ex.to_json())
    assert any(str(v).startswith("<error") for _, v in ex)


# -- verdicts ---------------------------------------------------------------


def test_verdict_rendering() -> None:
    env = Env(x=int)
    v = env.predicate("x > 1").always_true(assuming="x > -5")
    assert v.refuted
    assert "counterexample" in repr(v)
    assert "assuming: (x > -5)" in str(v)
    assert v._repr_markdown_().startswith("```")
    assert repr(Status.PROVED) == "Status.PROVED"
    sat = env.predicate("x > 1").satisfiable()
    assert sat.expect() is sat
    assert sat.counterexample is None
    assert sat.example == sat.witness
    assert "example" in str(sat)
    assert len(sat.witness or {}) == 1
    # every question's PROVED means the property asked holds, so expect() is never inverted
    errs = Env(x=int).compile("10 / x").never_errors()
    assert errs.refuted
    assert errs.counterexample == {"x": 0}
    with pytest.raises(VerificationFailed):
        errs.expect()
    unsat = env.predicate("x > 1 && x < 0").satisfiable()
    assert unsat.refuted
    assert unsat.example is None
    with pytest.raises(VerificationFailed):
        unsat.expect()


def test_verdict_unknown_and_timeout() -> None:
    timed_out = Verdict(Status.UNKNOWN, "q", reason="timeout after 1ms", bounded=True)
    with pytest.raises(VerificationTimeout):
        timed_out.expect()
    assert "bounded=True" in repr(timed_out)
    assert "unroll limit" in str(timed_out)
    with pytest.raises(VerificationFailed) as ei:
        Verdict(Status.REFUTED, "q").expect()
    assert ei.value.verdict.refuted


def test_evaluation_error_attributes() -> None:
    env = Env(x=int)
    with pytest.raises(CelEvaluationError) as ei:
        env.compile("x / 0").evaluate({"x": 1})
    e = ei.value
    assert e.message
    assert e.span[1] > e.span[0]
    assert e.expression_id >= 0


def test_compile_error_attributes() -> None:
    env = Env(x=int)
    with pytest.raises(CelTypeError) as ei:
        env.compile("y + z")
    e = ei.value
    assert e.message
    assert len(e.diagnostics) == 2
    assert [d.code for d in e.diagnostics] == ["type", "type"]
    assert str(e).startswith(e.diagnostics[0].rendered)
    assert str(e.diagnostics[0]) == e.diagnostics[0].rendered


# -- RuleSet & testing ------------------------------------------------------


def test_ruleset_surface() -> None:
    env = Env(x=int, y=int)
    old = RuleSet({"r": env.predicate("x > 1"), "q": env.compile("x / y"), "same": env.predicate("y > 0")})
    new = RuleSet(
        {"r": env.predicate("x > 2"), "same": env.predicate("0 < y"), "extra": env.predicate("true")}
    )
    assert len(old) == 3
    assert list(old) == ["r", "q", "same"]
    assert old["r"].source == "x > 1"
    assert set(old.may_error()) == {"q"}
    d = old.diff(new)
    assert set(d) == {"r"}
    assert d["r"][0].witness["x"] == 2
    ordered = old.check_pairwise(lambda a, b: a.implies(b), symmetric=False)
    assert ("r", "same") in ordered
    assert ("same", "r") in ordered
    with pytest.raises(ValueError, match="at least one"):
        RuleSet({})
    with pytest.raises(ValueError, match="same Env"):
        RuleSet({"a": env.predicate("x > 1"), "b": Env(z=int).predicate("z > 1")})
    scoped = RuleSet({"r": env.predicate("x > 1")}, assumptions=[env.predicate("x < 0")])
    assert scoped.assumptions == ("x < 0",)
    assert set(scoped.unreachable()) == {"r"}


def test_testing_helper_failures() -> None:
    env = Env(x=int)
    ct.assert_satisfiable(env.predicate("x > 1"))
    ct.assert_always(env.predicate("x > 1 || x <= 1"))
    with pytest.raises(AssertionError, match="never"):
        ct.assert_never(env.predicate("x > 1"))
    with pytest.raises(AssertionError, match="no evaluation errors"):
        ct.assert_no_errors(env.compile("10 / x"))


@dataclasses.dataclass
class Inner:
    v: int


@dataclasses.dataclass
class Outer:
    inner: Inner
    items: list[Inner]


def test_dataclass_with_nested_struct_roundtrip() -> None:
    env = Env(o=Outer)
    v = env.predicate("o.inner.v > 3 && size(o.items) == 1 && o.items[0].v == 2").satisfiable()
    assert v.proved
    assert v.witness is not None
    py = v.witness.to_python()["o"]
    assert isinstance(py, Outer)
    assert isinstance(py.inner, Inner)
    assert isinstance(py.items[0], Inner)
    assert env.expr("o", Outer).evaluate({"o": py}) == py


def test_local_dataclass_forward_refs() -> None:
    @dataclasses.dataclass
    class Leaf:
        v: int

    @dataclasses.dataclass
    class Tree:
        leaf: Leaf

    with pytest.raises(TypeError, match="cannot resolve annotation 'Leaf'"):
        Env(t=Tree)
    # declaring the dependency first makes it resolvable
    env = Env(leaf=Leaf, t=Tree)
    assert env.predicate("t.leaf.v == leaf.v").evaluate({"leaf": Leaf(1), "t": Tree(Leaf(1))}) is True


# -- M0 surface: from_model, Spec, diagnostic codes ---------------------------


def test_env_from_model() -> None:
    from pydantic import BaseModel

    class Ctx(BaseModel):
        total: Annotated[int, Field(ge=0, le=100)]
        tier: str
        timeout: int  # a field name never clashes with an option

    env = Env.from_model(Ctx, timeout=2.0)
    assert env.variables == {"total": "int", "tier": "string", "timeout": "int"}
    # the field's constraints survive (Pydantic moves Annotated metadata to FieldInfo)
    assert env.predicate("total > 100").satisfiable().refuted

    @dataclasses.dataclass
    class DCtx:
        total: Annotated[int, Field(ge=0, le=100)]

    assert Env.from_model(DCtx).predicate("total > 100").satisfiable().refuted
    with pytest.raises(TypeError, match="Pydantic model or dataclass"):
        Env.from_model(int)


def test_spec_validation_and_reuse() -> None:
    from celspresso import Spec

    env = Env(x=int)
    spec = Spec({"small": "x < 10"}, require=["x == 1"], examples=[({"x": 3}, True)], assumptions="x >= 0")
    assert spec.assumptions == ("x >= 0",)
    assert spec.check(env.predicate("x < 5")).ok
    assert not spec.check(env.predicate("x < 50")).ok
    # a list of invariants is still accepted where a Spec is
    assert env.check_rule("x < 5", ["x < 10"]).ok
    assert spec.assuming("x < 3").assumptions == ("x >= 0", "x < 3")
    with pytest.raises(TypeError, match="not a single string"):
        Spec("x < 10")  # type: ignore[arg-type]
    with pytest.raises(TypeError, match="CEL condition"):
        Spec([5])  # type: ignore[list-item]
    with pytest.raises(TypeError, match="examples"):
        Spec(examples=[{"x": 1}])  # type: ignore[list-item]


def test_diagnostic_codes() -> None:
    from celspresso import CelSubsetError, CelSyntaxError

    env = Env(x=int)
    with pytest.raises(CelSyntaxError) as syn:
        env.compile("x +")
    assert {d.code for d in syn.value.diagnostics} == {"syntax"}
    with pytest.raises(CelSubsetError) as sub:
        env.compile("double(x) > 1.0")
    assert isinstance(sub.value, CelTypeError)
    assert {d.code for d in sub.value.diagnostics} == {"subset"}
    assert str(sub.value).startswith("1:")  # the headline is the problem itself
    assert all(w.code == "lint" for w in env.predicate("x > 1 && x > 1").warnings)


def test_assumptions_follow_every_env_involved() -> None:
    env = Env(x=int)
    positive = env.assume("x > 0")
    base = env.predicate("100 / x > 0")
    # the env check_rule is called on brings its assumptions, whatever env compiled the rule
    assert positive.check_rule(base).ok
    assert not env.check_rule(base).ok
    # and an operand compiled under assumptions keeps them
    assert env.predicate("x > 5").implies(positive.predicate("x > 0")).proved
    assert positive.compile("100 / x").never_errors().proved
    # combining predicates keeps both sides' assumptions
    base = Env(x=int, y=int)
    p, q = base.assume("x > 0").predicate("x > 0"), base.assume("y > 0").predicate("y > 0")
    assert p.implies(q).proved
    assert (p & ~q).satisfiable().refuted
    with pytest.raises(ValueError, match="different Env"):
        positive.check_rule(Env(z=str).predicate("z == 'a'"))


def test_spec_is_a_read_only_value() -> None:
    from celspresso import Spec

    spec = Spec(["x < 10"], examples=[[{"x": 1}, True]])  # lists, as loaded from JSON
    assert spec.examples == (({"x": 1}, True),)
    with pytest.raises(TypeError):
        spec.invariants["y"] = "x > 0"  # type: ignore[index]
    with pytest.raises(TypeError, match="unhashable"):
        hash(spec)
    assert spec == Spec(["x < 10"], examples=[({"x": 1}, True)])
    with pytest.raises(TypeError, match="compiled Predicate"):
        spec.check("x < 5")  # type: ignore[arg-type]
    import copy
    import pickle

    assert copy.deepcopy(spec) == spec
    assert pickle.loads(pickle.dumps(spec)) == spec


def test_removed_env_options_say_so() -> None:
    with pytest.raises(TypeError, match="no longer an Env option"):
        Env(x=int, schema_constraints=False)  # type: ignore[arg-type]
    with pytest.raises(TypeError, match="no longer an Env option"):
        Env(x=int, debug_sample_proofs=3)  # type: ignore[arg-type]
    assert Env(schema_constraints=bool).variables == {"schema_constraints": "bool"}
    assert Env(schema_constraints=int | None).variables == {"schema_constraints": "int?"}
    with pytest.raises(TypeError, match=r"env\.assume"):
        Env(x=int).extend(assumptions={"x > 0"})
