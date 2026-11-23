"""How the verifier treats Python functions: opaque, tabulated, or written in CEL."""

import enum
from typing import Annotated, Literal

import pytest
from pydantic import Field

from celspresso import CelTypeError, Env, function

Pct = Annotated[int, Field(ge=0, le=100)]


# -- opaque: the prover never calls the function --------------------------------


def test_opaque_functions_are_never_called_while_solving() -> None:
    calls: list[int] = []

    @function
    def risk(n: int) -> int:
        calls.append(n)
        return n * 2

    env = Env(n=int).extend(functions=[risk])
    p = env.predicate("risk(n) > 10")
    assert p.evaluate({"n": 6}) is True
    calls.clear()
    v = p.satisfiable()
    # no guess-and-check: one replay at most, then an actionable UNKNOWN
    assert len(calls) <= 1
    assert v.unknown
    assert v.reason is not None
    assert "'risk'" in v.reason
    assert "ensures=" in v.reason
    assert "env.define" in v.reason
    # still deterministic: the same input gives the same output (or the same error)
    assert p.equivalent("risk(n) > 10 && risk(n) > 10").proved
    # a counterexample, when there is one, was replayed with the real function
    v = env.predicate("risk(n) > n").always_true()
    assert v.refuted or v.unknown
    if v.counterexample is not None:
        assert not risk(v.counterexample["n"]) > v.counterexample["n"]


def test_contracts_make_opaque_functions_provable() -> None:
    @function(ensures="result >= 0 && result <= 100", total=True)
    def score(n: int) -> int:
        return max(0, min(100, n))

    env = Env(n=int).extend(functions=[score])
    assert env.predicate("score(n) <= 100").always_true().proved


# -- tabulated: small finite inputs, called once each at declaration -------------


class Tier(enum.Enum):
    FREE = "free"
    PRO = "pro"


def test_small_int_domains_are_tabulated_once() -> None:
    calls: list[int] = []

    @function
    def twice(n: Annotated[int, Field(ge=0, le=3)]) -> int:
        calls.append(n)
        return n * 2

    env = Env(n=Annotated[int, Field(ge=0, le=3)]).extend(functions=[twice])
    assert sorted(calls) == [0, 1, 2, 3]  # every input, once, when declared
    calls.clear()
    v = env.predicate("twice(n) > 5").satisfiable()
    assert v.proved
    assert v.witness is not None
    assert v.witness["n"] == 3
    assert env.predicate("twice(n) == 2 * n").always_true().proved
    assert env.predicate("twice(n) == 7").satisfiable().refuted
    assert calls == [3]  # only the witness replay


def test_bool_literal_and_enum_parameters_are_tabulated() -> None:
    @function
    def limit(tier: Literal["free", "pro"], trial: bool) -> int:
        return {"free": 10, "pro": 1000}[tier] // (2 if trial else 1)

    @function
    def seats(tier: Tier) -> int:
        return 1 if tier is Tier.FREE or tier == "free" else 50

    env = Env(tier=Literal["free", "pro"], trial=bool, t=Tier).extend(functions=[limit, seats])
    assert env.predicate("limit(tier, trial) <= 1000").always_true().proved
    v = env.predicate("limit(tier, trial) == 500").satisfiable()
    assert v.witness == {"tier": "pro", "trial": True}
    assert env.predicate("seats(t) in [1, 50]").always_true().proved


def test_raising_inputs_become_errors() -> None:
    @function
    def inverse(n: Annotated[int, Field(ge=-2, le=2)]) -> int:
        return 100 // n

    env = Env(n=Annotated[int, Field(ge=-2, le=2)]).extend(functions=[inverse])
    v = env.expr("inverse(n)", int).never_errors()
    assert v.refuted
    assert v.witness == {"n": 0}
    assert env.predicate("n == 0 || inverse(n) != 0").always_true().proved


def test_tabulation_limits_and_opt_out() -> None:
    @function
    def big(a: Pct, b: Pct) -> int:  # 101 * 101 inputs: too many
        return a + b

    calls: list[int] = []

    @function(tabulate=False)
    def slow(n: Annotated[int, Field(ge=0, le=3)]) -> int:
        calls.append(n)
        return n

    env = Env(a=Pct, b=Pct, n=Annotated[int, Field(ge=0, le=3)]).extend(functions=[big, slow])
    assert calls == []
    assert env.predicate("big(a, b) == a + b").always_true().unknown
    assert env.predicate("slow(n) == n").always_true().unknown


def test_outside_the_table_is_opaque() -> None:
    @function
    def twice(n: Annotated[int, Field(ge=0, le=3)]) -> int:
        return n * 2

    env = Env(m=int).extend(functions=[twice])
    v = env.predicate("m < 0 || m > 3 || twice(m) == 2 * m").always_true()
    assert v.proved
    v = env.predicate("m < 0 || twice(m) == 2 * m").always_true()
    assert v.unknown
    assert v.reason is not None
    assert "outside its tabulated inputs" in v.reason


# -- written in CEL: parameterized definitions ------------------------------------


def test_parameterized_definitions_are_fully_verified() -> None:
    env = (
        Env(score=int, lo=int)
        .define("clamp", "v < 0 ? 0 : (v > 100 ? 100 : v)", params={"v": int})
        .define("between", "x >= a && x <= b", params={"x": int, "a": int, "b": int})
    )
    assert env.predicate("clamp(score) <= 100").always_true().proved
    # the body is seen exactly, overflow included: score * 2 can fail before clamping
    v = env.predicate("clamp(score * 2) <= 100").always_true()
    assert v.refuted
    assert v.counterexample is not None
    assert abs(v.counterexample["score"]) >= 2**62
    assert env.predicate("between(clamp(score), 0, 100)").always_true().proved
    p = env.predicate("clamp(score) == 100")
    assert p.evaluate({"score": 250}) is True
    assert p.evaluate({"score": 50}) is False
    v = env.predicate("clamp(score) == score").always_true()
    assert v.refuted
    assert v.counterexample is not None
    assert not 0 <= v.counterexample["score"] <= 100
    # arguments evaluate errors as CEL does: clamp(x) of an overflowing x errors
    assert env.expr("clamp(score * 4611686018427387904)", int).never_errors().refuted


def test_parameterized_definitions_are_hygienic_and_composable() -> None:
    env = (
        Env(xs=Annotated[list[int], Field(max_length=3)], v=Annotated[int, Field(ge=-1000, le=1000)])
        .define("anyAbove", "items.exists(v, v > t)", params={"items": list[int], "t": int})
        .define("lenient", "anyAbove(items, t - 1)", params={"items": list[int], "t": int})
    )
    # the outer `v` is passed in; the body's own `v` is a different variable
    p = env.predicate("anyAbove(xs, v)")
    assert p.evaluate({"xs": [1, 5], "v": 4}) is True
    assert p.evaluate({"xs": [1, 5], "v": 5}) is False
    assert env.predicate("anyAbove(xs, v)").implies("lenient(xs, v)").proved
    assert env.predicate("xs.exists(v, anyAbove(xs, v))").evaluate({"xs": [1, 5], "v": 0}) is True


def test_parameterized_definition_errors() -> None:
    env = Env(n=int)
    with pytest.raises(CelTypeError):
        env.define("f", "x + 'a'", params={"x": int})
    with pytest.raises(CelTypeError):
        env.define("f", "n + y", params={"x": int})  # y is not a parameter
    g = env.define("g", "x + 1", params={"x": int})
    with pytest.raises(CelTypeError):
        g.compile("g('a')")
    with pytest.raises(CelTypeError):
        g.compile("g(1, 2)")
    with pytest.raises(ValueError, match="parameter name"):
        env.define("h", "1", params={"not valid": int})
    with pytest.raises(ValueError, match="shadows a variable"):
        env.define("n", "x", params={"x": int})


def test_user_overload_on_a_builtin_name_gets_host_function_advice():
    @function(name="contains")
    def contains_n(s: str, n: int) -> bool:
        return True  # the solver can't know that, and its counterexample won't replay

    env = Env(s=str, n=int).extend(functions=[contains_n])
    reason = env.predicate("contains(s, n)").always_true().reason
    assert reason is not None
    assert "ensures=" in reason
    assert "doesn't model" not in reason


@function(ensures="result >= 0 && result < s.size()", total=True)
def _first_pos(s: str) -> int:
    return 0


def test_contracts_bind_only_calls_that_happen() -> None:
    # the contract can't hold for '', and no call below is ever made on ''
    env = Env(s=str).extend(functions=[_first_pos])
    assert env.predicate("s == '' && (s.size() > 0 ? _first_pos(s) == 0 : true)").satisfiable().proved
    assert env.predicate("s == '' && !(s != '' && _first_pos(s) < 0)").satisfiable().proved
    assert env.predicate("s != ''").always_true(assuming="s.size() == 0 ? true : _first_pos(s) >= 0").refuted
    # where the call does happen, the contract is used
    assert env.predicate("s.size() > 0 ? _first_pos(s) >= 0 : true").always_true().proved


def test_contracts_inside_a_comprehension_skip_slots_that_dont_exist() -> None:
    word = Annotated[str, Field(min_length=1, max_length=4)]
    env = Env(ws=Annotated[list[word], Field(max_length=3)]).extend(functions=[_first_pos])
    p = env.predicate("ws.all(w, _first_pos(w) >= 0) && ws.size() == 3")
    v = p.always_true()
    assert v.refuted
    assert not p.evaluate(v.counterexample)
