"""Vetting provider-credentialing rules written by customers or an LLM.

A healthcare back-office platform lets each customer (or an agent drafting from a payer's
policy manual) configure when a provider may be scheduled. The platform owns a few
compliance invariants that no configured rule may break. celspresso checks each draft
before it goes live and explains every rejection with a concrete provider.

Run with:  uv run python examples/credentialing.py
"""

from __future__ import annotations

from datetime import date
from typing import Annotated, Literal

from pydantic import BaseModel, Field

from celspresso import Env


class Provider(BaseModel):
    type: Literal["MD", "DO", "NP", "PA"]
    status: Literal["applied", "provisional", "credentialed", "denied"]
    state: Literal["OH", "TX", "CA", "NY", "FL"]
    applied_on: date
    license_expires: date
    oig_cleared: bool
    malpractice_claims: Annotated[int, Field(ge=0, le=20)]
    work_gap_months: Annotated[int, Field(ge=0, le=120)]
    board_certified: bool
    has_collab_agreement: bool


env = Env(p=Provider, today=date)

# Owned by the platform's compliance team; every configured rule must imply each one.
INVARIANTS = {
    "license is current": "p.license_expires >= today",
    "OIG exclusion screening passed": "p.oig_cleared",
    "NPs in OH/TX/CA have a collaborative agreement": (
        "p.type != 'NP' || !(p.state in ['OH', 'TX', 'CA']) || p.has_collab_agreement"
    ),
}

# What an LLM might produce on successive attempts, each after reading the previous report.
DRAFTS = [
    # a misspelled field
    "p.status == 'credentialed' && p.licence_expires >= today",
    # a provisional-privileges exception (NCQA allows up to 60 days) that skips every check
    """p.status == 'credentialed' && p.license_expires >= today && p.oig_cleared
       || p.status == 'provisional' && p.applied_on.daysUntil(today) <= 60""",
    # license and OIG fixed; the NP supervision requirement forgotten
    """(p.status == 'credentialed' || p.status == 'provisional' && p.applied_on.daysUntil(today) <= 60)
       && p.license_expires >= today && p.oig_cleared""",
    # accepted
    """(p.status == 'credentialed' || p.status == 'provisional' && p.applied_on.daysUntil(today) <= 60)
       && p.license_expires >= today && p.oig_cleared
       && (p.type != 'NP' || !(p.state in ['OH', 'TX', 'CA']) || p.has_collab_agreement)""",
]


def repair_loop() -> None:
    print("== Scheduling rule, drafted by an agent ==\n")
    for attempt, src in enumerate(DRAFTS, 1):
        report = env.check_rule(src, INVARIANTS)
        print(f"attempt {attempt}: {report}\n")
        if report.ok:
            break
        # in a real system: feedback = str(report); src = llm.redraft(policy, feedback)


def review_a_change() -> None:
    print("== Reviewing an 'equivalent' simplification of committee routing ==\n")
    old = env.predicate(
        "p.malpractice_claims == 0 && p.work_gap_months <= 6 && p.board_certified && p.oig_cleared"
    )
    new = env.predicate("p.malpractice_claims <= 1 && p.work_gap_months < 12 && p.oig_cleared")
    print("equivalent:", old.equivalent(new).status.name)
    print("files that now skip committee review, one per distinct reason:")
    for d in old.diff(new):
        print("  ", d)


if __name__ == "__main__":
    repair_loop()
    review_a_change()
