"""Specs on computed values: check_rule on rules that give an amount, a label or a struct,
with `ensures` over `result`, `returns` and value examples."""

import dataclasses
import enum
import pickle
from decimal import Decimal
from typing import Annotated, Literal

import pytest
from pydantic import BaseModel, Field

from celspresso import CelSubsetError, Env, RuleCheck, Spec, function
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
    with pytest.raises(ValueError, match="variable or definition named 'result'"):
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


class Tight(BaseModel):
    action: Literal["refund", "deny"]
    amount: Annotated[int, Field(ge=0)]
    tags: Annotated[list[Annotated[str, Field(max_length=3)]], Field(max_length=2)]


def test_a_built_result_must_meet_its_class_constraints() -> None:
    # inputs are assumed to meet their constraints, but a value the rule builds is checked,
    # or the rule would pass every check and then fail to become a Python value
    tight = Env(o=Order, structs=[Tight])
    spec = Spec(returns=Tight, examples=[(LOST, {"action": "deny", "amount": 10, "tags": ["a"]})])
    ok = "Tight{action: o.status == 'lost' ? 'deny' : 'refund', amount: o.total, tags: ['a']}"
    assert tight.check_rule(ok, spec).ok
    for bad, what in [
        ("Tight{action: 'oops', amount: 0, tags: []}", "the result.action is one of"),
        ("Tight{action: 'deny', amount: o.total - 1, tags: []}", "the result.amount >= 0"),
        ("Tight{action: 'deny', amount: 0, tags: [o.status]}", "each item of the result.tags has size <= 3"),
        ("Tight{action: 'deny', amount: 0, tags: o.items.map(x, 'a')}", "the result.tags has size <= 2"),
    ]:
        r = tight.check_rule(bad, Spec(returns=Tight))
        assert kinds(r) == ["violates"], (bad, str(r))
        assert "isn't a valid Tight" in str(r)
        assert what in str(r), (bad, str(r))
    # an example on such a rule reports the failure instead of raising
    r = tight.check_rule("Tight{action: 'oops', amount: 0, tags: []}", spec)
    assert "wrong_example" in kinds(r)
    assert "can't be built" in str(r)
    # the constraints of returns itself, and in a list of structs
    nonneg = Spec(returns=Annotated[int, Field(ge=0)])
    assert kinds(env.check_rule("o.total - 1", nonneg)) == ["violates"]
    assert env.check_rule("o.total", nonneg).ok
    many = "o.items.map(x, Tight{action: 'deny', amount: x - 1, tags: []})"
    r = tight.check_rule(many, Spec(returns=list[Tight]))
    assert "each item of the result.amount >= 0 fails" in str(r)
    # the size of a list inside a struct inside a list isn't known statically: unverified
    assert kinds(r) == ["violates", "unverified", "unverified"]
    assert "can't bound the size" in str(r)


def test_rules_and_conditions_may_end_in_a_comment() -> None:
    r = env.check_rule("o.total // the whole order", Spec(ensures=["result <= o.total // capped"]))
    assert r.ok, str(r)


def test_examples_compare_nested_values_exactly() -> None:
    assert kinds(env.check_rule("[o.total > 0]", Spec(examples=[(LOST, [1])], returns=list[bool]))) == [
        "wrong_example"
    ]
    rule = "[Decision{action: 'deny', amount: 0}]"
    spec = Spec(returns=list[Decision], examples=[(LOST, [{"action": "deny", "amount": 0}])])
    assert env.check_rule(rule, spec).ok, str(env.check_rule(rule, spec))
    spec = Spec(returns=list[Decision], examples=[(LOST, [Decision(action="deny", amount=0)])])
    assert env.check_rule(rule, spec).ok


def test_result_may_not_be_a_definition_either() -> None:
    with pytest.raises(ValueError, match="variable or definition named 'result'"):
        env.define("result", "1").check_rule("o.total", Spec(ensures=["result > 0"]))


def test_fields_of_a_built_struct_are_bounded_by_what_built_them() -> None:
    tight = Env(o=Order, structs=[Tight])
    built = "Tight{action: 'deny', amount: 0, tags: o.items.map(x, 'a')}"
    assert tight.predicate(f"size({built}.tags) <= 4").always_true().proved
    assert (
        tight.predicate(f"cel.bind(t, o.total > 5 ? {built} : {built}, size(t.tags) <= 4)")
        .always_true()
        .proved
    )

    # a struct from a function has no known size: its list fields stay unbounded
    @function
    def make(n: int) -> Tight:
        return Tight(action="deny", amount=n, tags=[])

    with pytest.raises(CelSubsetError, match="can't bound"):
        tight.extend(functions=[make]).predicate("size(make(1).tags) <= 4")


class Color(enum.Enum):
    R = "r"
    G = "g"


class Odd(BaseModel):
    pair: tuple[int, int]
    big: Annotated[int, Field(ge=2**53)]
    huge: Annotated[int, Field(le=2**70)]
    color: Color
    seen: set[int]


def test_built_results_check_exact_bounds_lengths_and_compare_enums_and_sets() -> None:
    odd = Env(o=Order, structs=[Odd])
    good = "Odd{pair: [1, 2], big: 9007199254740992, huge: o.total, color: 'r', seen: [2, 1]}"
    spec = Spec(
        returns=Odd,
        examples=[(LOST, {"pair": (1, 2), "big": 2**53, "huge": 10, "color": "r", "seen": [1, 2]})],
    )
    assert odd.check_rule(good, spec).ok, str(odd.check_rule(good, spec))
    # a tuple's length, and an int bound past 2**53, are checked exactly
    r = odd.check_rule(good.replace("[1, 2]", "[1, 2, 3]"), Spec(returns=Odd))
    assert "the result.pair has size <= 2 fails" in str(r)
    r = odd.check_rule(good.replace("9007199254740992", "9007199254740991"), Spec(returns=Odd))
    assert "the result.big >= 9007199254740992 fails" in str(r)

    # a bound a double can't hold is refused, never rounded
    class Inexact(BaseModel):
        n: Annotated[int, Field(ge=2**53 + 1)]

    with pytest.raises(ValueError, match="not exactly representable"):
        Env(i=Inexact)
    # a rule that reads no input says so
    const = env.check_rule("-1", Spec(returns=Annotated[int, Field(ge=0)]))
    assert "isn't a valid int on every input: the result >= 0 fails" in str(const)
