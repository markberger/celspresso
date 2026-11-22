"""Vetting rules you didn't write: check_rule, behaviour-class diffs, readable witnesses."""

import datetime as dt
from typing import Annotated, Literal

import pytest
from pydantic import BaseModel, Field

from celspresso import Env, Problem, RuleCheck


class Provider(BaseModel):
    type: Literal["MD", "NP"]
    status: Literal["applied", "provisional", "credentialed"]
    state: Literal["OH", "NY"]
    applied_on: dt.date
    license_expires: dt.date
    oig_cleared: bool
    malpractice_claims: Annotated[int, Field(ge=0, le=20)]
    work_gap_months: Annotated[int, Field(ge=0, le=120)]
    board_certified: bool
    has_collab_agreement: bool


env = Env(p=Provider, today=dt.date, m=dict[str, int])
INVARIANTS = {
    "license is current": "p.license_expires >= today",
    "OIG screening passed": "p.oig_cleared",
    "NP supervision": "p.type != 'NP' || p.state != 'OH' || p.has_collab_agreement",
}
SAFE = """(p.status == 'credentialed' || p.status == 'provisional' && p.applied_on.daysUntil(today) <= 60)
          && p.license_expires >= today && p.oig_cleared
          && (p.type != 'NP' || p.state != 'OH' || p.has_collab_agreement)"""


def kinds(r: RuleCheck) -> list[str]:
    return [p.kind for p in r.problems]


def test_accepts_a_rule_that_satisfies_every_invariant() -> None:
    r = env.check_rule(SAFE, INVARIANTS)
    assert r.ok
    assert r.rule is not None
    assert str(r).startswith("accepted")
    with pytest.raises(TypeError, match=r"RuleCheck\.ok"):
        bool(r)


def test_invalid_rules_report_the_compile_error() -> None:
    r = env.check_rule("p.licence_expires >= today", INVARIANTS)
    assert kinds(r) == ["invalid"]
    assert r.rule is None
    assert "did you mean 'license_expires'" in str(r)
    assert kinds(env.check_rule("p.malpractice_claims + 1")) == ["invalid"]  # not a predicate


def test_violations_name_the_invariant_and_show_relevant_values() -> None:
    r = env.check_rule("p.status == 'provisional' && p.applied_on.daysUntil(today) <= 60", INVARIANTS)
    assert kinds(r) == ["violates"] * 3
    p = r.problems[0]
    assert p.invariant == "license is current"
    assert p.verdict is not None
    assert p.verdict.refuted
    assert "p.status = 'provisional'" in p.message
    assert "work_gap_months" not in p.message  # irrelevant fields are left out


def test_invariants_may_be_unnamed_predicates() -> None:
    inv = env.predicate("p.oig_cleared")
    r = env.check_rule("p.status == 'credentialed'", [inv])
    assert [p.invariant for p in r.problems] == ["p.oig_cleared"]


def test_dead_and_crashing_rules() -> None:
    assert kinds(env.check_rule("p.work_gap_months > 200")) == ["never_fires"]
    r = env.check_rule("100 / p.work_gap_months > 1")
    assert kinds(r) == ["can_error"]
    assert "p.work_gap_months = 0" in str(r)


def test_assumptions_apply_to_every_check() -> None:
    r = env.check_rule("p.status == 'credentialed'", INVARIANTS, assuming=["p.oig_cleared", SAFE])
    assert r.ok


def test_unknown_is_never_accepted() -> None:
    # m has no max_length, so "every entry" can only be checked up to the unroll limit
    r = env.check_rule("m.all(k, m[k] >= 0)", ["m.all(k, m[k] >= 0)"])
    assert r.problems
    assert set(kinds(r)) == {"unverified"}
    assert isinstance(r.problems[0], Problem)
    assert "unroll limit" in r.problems[0].message


def test_diff_returns_one_witness_per_behaviour() -> None:
    old = env.predicate(
        "p.malpractice_claims == 0 && p.work_gap_months <= 6 && p.board_certified && p.oig_cleared"
    )
    new = env.predicate("p.malpractice_claims <= 1 && p.work_gap_months < 12 && p.oig_cleared")
    found = old.diff(new, limit=10)
    reasons = set()
    for w in found:
        p = w["p"]
        assert old.evaluate(dict(w)) != new.evaluate(dict(w))
        reasons.add(
            "claim" if p["malpractice_claims"] == 1 else "gap" if p["work_gap_months"] > 6 else "board"
        )
    assert len(found) == 3
    assert reasons == {"claim", "gap", "board"}


def test_diff_of_arithmetic_falls_back_to_values() -> None:
    a = env.expr("p.work_gap_months * 2", int)
    b = env.expr("p.work_gap_months + 2", int)
    assert len(a.diff(b, limit=3)) == 3


def test_witness_dates_are_near_today() -> None:
    v = env.predicate("p.license_expires >= today").always_true()
    assert v.counterexample is not None
    rel = v.counterexample.relevant
    assert set(rel) == {"p.license_expires", "today"}
    for d in rel.values():
        assert abs((d - dt.date.today()).days) <= 400
    assert "today = " in str(v.counterexample)
    assert "p.license_expires = " in str(v)
