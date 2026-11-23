"""Assertion helpers for test suites: `assert_equivalent(a, b)` etc.

Each raises `VerificationFailed` (an AssertionError) with a readable counterexample.
"""

from __future__ import annotations

from typing import TYPE_CHECKING, Any

from ._errors import VerificationFailed

if TYPE_CHECKING:
    from ._env import Expr, Predicate
    from ._verdict import Verdict

__all__ = [
    "assert_always",
    "assert_equivalent",
    "assert_implies",
    "assert_never",
    "assert_no_errors",
    "assert_satisfiable",
]


def assert_equivalent(a: Expr[Any], b: Expr[Any] | str, **kw: Any) -> Verdict:
    return a.equivalent(b, **kw).expect()


def assert_implies(a: Predicate, b: Predicate | str, **kw: Any) -> Verdict:
    return a.implies(b, **kw).expect()


def assert_satisfiable(p: Predicate, **kw: Any) -> Verdict:
    return p.satisfiable(**kw).expect()


def assert_always(p: Predicate, **kw: Any) -> Verdict:
    return p.always_true(**kw).expect()


def assert_never(p: Predicate, **kw: Any) -> Verdict:
    v = p.satisfiable(**kw)
    if not v.refuted:
        raise VerificationFailed(v, f"expected never true, got:\n{v}")
    return v


def assert_no_errors(e: Expr[Any], **kw: Any) -> Verdict:
    v = e.never_errors(**kw)
    if not v.proved:
        raise VerificationFailed(v, f"expected no evaluation errors, got:\n{v}")
    return v
