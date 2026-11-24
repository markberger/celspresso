"""Milestone 3 verifier features: bounds, function contracts, proof sampling, verify_all."""

import datetime as dt
from typing import Annotated, Literal

import pytest
from pydantic import BaseModel, Field

from celspresso import Bounds, CelEvaluationError, CelSubsetError, CelTypeError, Env, RuleSet, function
from celspresso._env import _debug_options


class Order(BaseModel):
    total_cents: Annotated[int, Field(ge=0, le=10_000_000)]
    days: Annotated[int, Field(ge=0, le=365)]
    tier: Literal["standard", "gold"]
    items: Annotated[list[int], Field(max_length=4)]
    notes: list[str]


env = Env(order=Order, today=dt.date)


def test_bounds_are_proved_and_attained() -> None:
    b = env.expr("order.tier == 'gold' ? order.total_cents / 10 : 0", int).bounds()
    assert isinstance(b, Bounds)
    assert b.proved
    assert b.expect() == (0, 1_000_000)
    assert b.max is not None
    assert b.max.witness.relevant == {
        "order.tier": "gold",
        "order.total_cents": 10_000_000,
    }
    assert str(b) == "[0, 1000000]"
    with pytest.raises(TypeError):
        bool(b)


def test_bounds_respect_assumptions_and_max_length() -> None:
    assert env.expr("order.days").bounds(assuming="order.days > 100").expect() == (101, 365)
    b = env.expr("order.items.size()").bounds()
    assert b.expect() == (0, 4)
    assert b.max is not None
    assert b.max.witness.to_python()["order"].items == [0, 0, 0, 0]


def test_bounds_explain_what_is_missing() -> None:
    with pytest.raises(CelSubsetError, match=r"'order\.notes': it has no max_length"):
        env.expr("size(order.notes)")
    assert "integer-valued" in (env.expr("order.tier").bounds().reason or "")
    assert env.expr("order.days / 0").bounds().min is None


def test_ensures_contracts_and_total_functions() -> None:
    @function(ensures="result >= 0 && result <= 100", total=True)
    def risk(score: int) -> int:
        return min(100, max(0, score))

    @function(ensures="result >= 0")
    def fee(cents: int) -> int:
        return cents // 100

    e = Env(x=int).extend(functions=[risk, fee])
    assert e.predicate("risk(x) * 2 <= 200").always_true().proved
    # the contract allows it, but only the real function could say which x: not UNSAT
    assert not e.predicate("risk(x) > 50").satisfiable().refuted
    assert e.predicate("risk(x) > 100").satisfiable().refuted
    # fee's contract is wrong (fee(-100) == -1). Contracts are trusted, so the prover
    # can't catch that; here fee may also fail (no total=True), so this isn't PROVED,
    # and any counterexample it reports has been replayed with the real function
    v = e.predicate("fee(x) >= 0").always_true()
    assert not v.proved
    if v.counterexample is not None:
        assert fee(v.counterexample["x"]) < 0
    assert any(
        "ensures contract of 'risk'" in a
        for a in e.predicate("risk(x) >= 0").always_true().stats.approximations
    )


def test_bad_contracts_are_rejected() -> None:
    @function(ensures="result >= 'a'")
    def g(x: int) -> int:
        return x

    with pytest.raises(CelTypeError) as exc:
        Env(x=int).extend(functions=[g])
    assert exc.value.source == "result >= 'a'"

    @function(ensures="result + 1")
    def h(x: int) -> int:
        return x

    with pytest.raises(ValueError, match="bool expression"):
        Env(x=int).extend(functions=[h])

    @function(ensures="result > 0")
    def k(result: int) -> int:
        return result

    with pytest.raises(TypeError, match="clashes"):
        Env(x=int).extend(functions=[k])


def test_proof_sampling() -> None:
    sampled = _debug_options(Env(x=int, y=int), sample_proofs=10)
    assert sampled.predicate("x < y || x >= y").always_true().proved
    with pytest.raises(TypeError, match="sample_proofs"):
        _debug_options(Env(x=int), sample_proofs=-1)


def test_ruleset_verify_all() -> None:
    rs = RuleSet(
        {
            "small": env.predicate("order.total_cents <= 1000"),
            "gold": env.predicate("order.tier == 'gold'"),
            "fee": env.expr("order.days * 2"),
        },
        assumptions=["order.days < 30"],
    )
    checks = rs.verify_all({"cheap": "order.total_cents <= 5000"})
    assert set(checks) == {"small", "gold"}
    assert checks["small"].ok
    assert not checks["gold"].ok


def test_comprehensions_over_a_nullable_list() -> None:
    class Tagged(BaseModel):
        tags: Annotated[list[str], Field(max_length=3)] | None = None

    e = Env(t=Tagged)
    guarded = e.predicate("t.tags == null || t.tags.all(x, x.startsWith('x'))")
    assert guarded.never_errors().proved
    assert guarded.always_true().refuted
    # iterating a null is an error, as in the evaluator
    bare = e.predicate("t.tags.all(x, x.startsWith('x'))")
    v = bare.never_errors()
    assert v.refuted
    assert v.counterexample is not None
    assert v.counterexample.relevant == {"t.tags": None}
    found = e.predicate("t.tags != null && t.tags.exists(x, x == 'y') && size(t.tags) == 2").satisfiable()
    assert found.proved


def test_an_unused_argument_that_fails_still_fails() -> None:
    # the evaluator computes bound values (and a definition's arguments) up front, so the
    # verifier must count their errors even when nothing reads them
    env = Env(x=int).define("always_one", "1", params={"v": int})
    for src in ("cel.bind(r, 10 / x, true)", "always_one(10 / x) == 1"):
        p = env.predicate(src)
        v = p.never_errors()
        assert v.refuted, src
        assert v.counterexample == {"x": 0}, src
        with pytest.raises(CelEvaluationError):
            p.evaluate({"x": 0})
