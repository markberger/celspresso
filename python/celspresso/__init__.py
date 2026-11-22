"""celspresso: CEL expressions for Python, type-checked and formally verified."""

from __future__ import annotations

from importlib.metadata import PackageNotFoundError, version

from ._env import Env, Explanation, Expr, Limits, Predicate, Problem, RuleCheck, function
from ._errors import (
    CelError,
    CelEvaluationError,
    CelSyntaxError,
    CelTypeError,
    Diagnostic,
    VerificationFailed,
    VerificationTimeout,
)
from ._ruleset import RuleSet
from ._verdict import Bounds, Extreme, Stats, Status, Verdict, Witness

try:
    __version__ = version("celspresso")
except PackageNotFoundError:  # pragma: no cover
    __version__ = "0.0.0"

__all__ = [
    "Bounds",
    "CelError",
    "CelEvaluationError",
    "CelSyntaxError",
    "CelTypeError",
    "Diagnostic",
    "Env",
    "Explanation",
    "Expr",
    "Extreme",
    "Limits",
    "Predicate",
    "Problem",
    "RuleCheck",
    "RuleSet",
    "Stats",
    "Status",
    "Verdict",
    "VerificationFailed",
    "VerificationTimeout",
    "Witness",
    "function",
]
