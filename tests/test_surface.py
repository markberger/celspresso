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
    assert env.predicate("c == 'green'").satisfiable().unsat
    assert env.predicate("lv == 2").satisfiable().unsat
    assert env.predicate("n == 2").satisfiable().sat
    assert env.predicate("n == 3").satisfiable().unsat


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
    assert env.predicate("p.addr.zip == '1234'").satisfiable().unsat
    assert env.predicate("p.addr.zip.startsWith('9')").satisfiable().sat
    out = env.expr("p", Person).evaluate(
        {"p": Person(addr=Addr(zip="12345"), tags={"a": 1}), "other": {"line": "x"}}
    )
    assert isinstance(out.addr, Addr)


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
        env.extend(assumptions=["x + 1"])

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
    dyn = env.expr("d['k']", int)  # dyn is accepted for any requested type
    assert dyn.output_type == "dyn"
    assert isinstance(env.expr("d['k']", bool), Predicate)


# -- expressions ------------------------------------------------------------


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
    ws = env.predicate("x > 1").diff(env.predicate("x > 3"), limit=5)
    assert sorted(w["x"] for w in ws) == [2, 3]


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
    assert repr(Status.SAT) == "Status.SAT"
    sat = env.predicate("x > 1").satisfiable()
    assert sat.expect() is sat
    assert sat.counterexample is None
    assert "witness" in str(sat)
    assert len(sat.witness or {}) == 1


def test_verdict_unknown_and_timeout() -> None:
    timed_out = Verdict(Status.UNKNOWN, "q", reason="timeout after 1ms", bounded=True)
    with pytest.raises(VerificationTimeout):
        timed_out.expect()
    assert "bounded=True" in repr(timed_out)
    assert "unroll limit" in str(timed_out)
    with pytest.raises(VerificationFailed) as ei:
        Verdict(Status.UNSAT, "q").expect()
    assert ei.value.verdict.unsat


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
    assert "2 errors" in str(e)
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
    assert set(old.can_error()) == {"q"}
    d = old.diff(new)
    assert set(d) == {"r"}
    assert d["r"][0]["x"] == 2
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
    assert v.sat
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
