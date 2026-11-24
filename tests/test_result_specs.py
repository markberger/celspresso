"""Specs on computed values: check_rule on rules that give an amount, a label or a struct,
with `ensures` over `result`, `returns` and value examples."""

import dataclasses
import pickle
from decimal import Decimal
from typing import Annotated, Literal

import pytest
from pydantic import BaseModel, Field

from celspresso import CelSubsetError, Env, RuleCheck, Spec
from celspresso.schema import T


class Order(BaseModel):
    total: Annotated[int, Field(ge=0, le=100_000)]
    status: Annotated[str, Field(max_length=10)]
    items: Annotated[list[Annotated[int, Field(ge=0, le=1000)]], Field(max_length=4)]


class Decision(BaseModel):
    action: Literal["refund", "deny", "escalate"]
    amount: int


@dataclasses.dataclass
class Route:
    queue: str
    priority: int


env = Env(o=Order, structs=[Decision, Route])
LOST = {"o": {"total": 10, "status": "lost", "items": []}}
DECISION_SPEC = Spec(
    ensures={
        "no over-refund": "result.amount >= 0 && result.amount <= o.total",
        "deny pays nothing": "result.action != 'deny' || result.amount == 0",
    },
    returns=Decision,
    examples=[(LOST, {"action": "refund", "amount": 10})],
)
GOOD = (
    "o.status == 'lost' ? Decision{action: 'refund', amount: o.total} : Decision{action: 'deny', amount: 0}"
)


def kinds(r: RuleCheck) -> list[str]:
    return [p.kind for p in r.problems]


def test_a_decision_rule_that_meets_its_spec_is_accepted() -> None:
    r = env.check_rule(GOOD, DECISION_SPEC)
    assert r.ok, str(r)
    assert r.rule is not None
    assert r.rule.output_type == "Decision"
    assert DECISION_SPEC.check(env.compile(GOOD)).ok


def test_a_broken_guarantee_names_it_with_the_input_and_the_result() -> None:
    bad = GOOD.replace("amount: 0", "amount: 1")
    r = env.check_rule(bad, DECISION_SPEC)
    assert kinds(r) == ["violates", "violates"]
    over, deny = r.problems
    assert over.invariant == "no over-refund"
    assert deny.invariant == "deny pays nothing"
    assert "the result is Decision(action='deny', amount=1)" in deny.message
    assert deny.verdict is not None
    w = deny.verdict.counterexample
    assert w is not None
    assert env.compile(bad).evaluate(w).amount == 1


def test_scalar_results_and_labels() -> None:
    refund = "o.status == 'lost' ? o.total : o.total / 2"
    capped = Spec(ensures=["result >= 0 && result <= o.total"], returns=int)
    assert env.check_rule(refund, capped).ok
    over = env.check_rule("o.total + 1", capped)
    assert kinds(over) == ["violates"]
    assert "the result is 1" in over.problems[0].message
    label = "o.total > 500 ? 'review' : 'auto'"
    assert env.check_rule(label, Spec(ensures=["result in ['review', 'auto']"])).ok
    assert kinds(env.check_rule(label, Spec(ensures=["result == 'auto'"]))) == ["violates"]


def test_ensures_skip_inputs_on_which_the_rule_fails() -> None:
    # the division fails at total 0: that is reported once, as may_error, and the
    # guarantee is checked only where the rule has a value
    r = env.check_rule("1000 / o.total", Spec(ensures={"bounded": "result <= 1000"}))
    assert kinds(r) == ["may_error"]
    r = env.check_rule("1000 / o.total", Spec(ensures={"positive": "result > 0"}))
    assert kinds(r) == ["may_error", "violates"]
    assert "the result is 0" in r.problems[1].message


def test_struct_results_from_dataclasses_and_lists() -> None:
    route = "o.total > 500 ? Route{queue: 'review', priority: 1} : Route{queue: 'auto', priority: 3}"
    spec = Spec(ensures={"urgent review": "result.queue != 'review' || result.priority == 1"}, returns=Route)
    assert env.check_rule(route, spec).ok
    r = env.check_rule(route, Spec(examples=[(LOST, {"queue": "auto", "priority": 3})], returns=Route))
    assert r.ok, str(r)
    # a list result is bounded by the rule, so a condition over it compiles and is decided
    doubled = "o.items.map(x, x * 2)"
    assert env.check_rule(doubled, Spec(ensures=["result.all(x, x <= 2000)"])).ok
    assert kinds(env.check_rule(doubled, Spec(ensures=["result.all(x, x <= 1000)"]))) == ["violates"]


def test_wrong_result_types_are_invalid() -> None:
    r = env.check_rule("o.total / 2", DECISION_SPEC)
    assert kinds(r) == ["invalid"]
    assert "expected Decision" in str(r)
    # without returns, a condition that doesn't fit the result's type says so
    r = env.check_rule("o.total / 2", Spec(ensures={"capped": "result.amount <= o.total"}))
    assert kinds(r) == ["invalid"]
    assert r.problems[0].invariant == "capped"
    assert "doesn't apply to this rule's result (int)" in str(r)


def test_value_rules_need_a_spec_about_values() -> None:
    # a gate written for true/false rules never passes a rule that computes a value
    r = env.check_rule("o.total + 1")
    assert kinds(r) == ["invalid"]
    assert "not true or false" in str(r)
    r = env.check_rule("o.total + 1", {"positive": "o.total > 0"})
    assert kinds(r) == ["invalid"]
    assert "invariants and require apply only" in str(r)
    assert env.check_rule("o.total + 1", Spec(returns=int)).ok
    # and returns=bool keeps a predicate gate strict
    assert kinds(env.check_rule("o.total", Spec(returns=bool))) == ["invalid"]


def test_value_examples() -> None:
    spec = Spec(returns=int, examples=[(LOST, 10), (LOST, 11)])
    r = env.check_rule("o.total", spec)
    assert kinds(r) == ["wrong_example"]
    assert "example 1 should give 11, but the rule gives 10" in str(r)
    # booleans don't match ints (True == 1 in Python)
    r = env.check_rule("o.total > 0", Spec(examples=[(LOST, 1)]))
    assert kinds(r) == ["wrong_example"]
    # a struct result matches an instance or a mapping of its fields
    as_model = Spec(returns=Decision, examples=[(LOST, Decision(action="refund", amount=10))])
    assert env.check_rule(GOOD, as_model).ok
    wrong = Spec(returns=Decision, examples=[(LOST, {"action": "deny", "amount": 0})])
    assert kinds(env.check_rule(GOOD, wrong)) == ["wrong_example"]


def test_fixed_point_results() -> None:
    money = Env(total=T.fixed(10, 2))
    example = ({"total": Decimal("9.99")}, Decimal("4.99"))
    spec = Spec(ensures=["result <= total"], returns=T.fixed(10, 2), examples=[example])
    # a fixed-point value may be negative: half of -0.01 rounds to 0.00, above it
    r = money.check_rule("total / 2", spec)
    assert kinds(r) == ["violates"]
    assert "Decimal('0.00')" in str(r)
    assert money.check_rule("total / 2", spec.assuming("total >= 0")).ok


def test_result_is_reserved_when_ensures_are_given() -> None:
    clash = Env(result=int)
    with pytest.raises(ValueError, match="variable named 'result'"):
        clash.check_rule("result + 1", Spec(ensures=["result > 0"]))
    assert clash.check_rule("result / 2", Spec(returns=int)).ok


def test_structs_accepts_classes() -> None:
    assert env.compile("Decision{action: 'deny', amount: 0}").output_type == "Decision"
    assert "Route" in env.describe()
    with pytest.raises(TypeError, match="not a struct type"):
        Env(structs=[int])
    with pytest.raises(TypeError, match="Struct values or classes"):
        Env(structs=["Decision"])
    # extend() too, and a class already used by a variable keeps its name
    e = Env(o=Order).extend(structs=[Decision], d=Decision)
    assert e.variables["d"] == "Decision"


def test_spec_round_trips() -> None:
    assert pickle.loads(pickle.dumps(DECISION_SPEC)) == DECISION_SPEC
    assert DECISION_SPEC.assuming("o.total < 50").returns is Decision


def test_a_struct_literal_sets_every_field() -> None:
    # unset fields have no value to read or to return, so leaving one out is rejected
    with pytest.raises(CelSubsetError, match=r"leaves out field 'amount'.*set it"):
        env.compile("Decision{action: 'deny'}")
    with pytest.raises(CelSubsetError, match="fields 'queue', 'priority'"):
        env.compile("Route{}")
    r = env.check_rule("Decision{action: 'deny'}", DECISION_SPEC)
    assert kinds(r) == ["invalid"]
