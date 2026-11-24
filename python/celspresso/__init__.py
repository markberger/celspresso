"""celspresso: CEL expressions for Python, type-checked and formally verified."""

from __future__ import annotations

from importlib.metadata import PackageNotFoundError, version

from ._env import Env, Explanation, Expr, Limits, Predicate, Problem, RuleCheck, function
from ._errors import (
    CelError,
    CelEvaluationError,
    CelSubsetError,
    CelSyntaxError,
    CelTypeError,
    Diagnostic,
    VerificationFailed,
    VerificationTimeout,
)
from ._ruleset import RuleSet
from ._spec import Spec
from ._table import NoRowMatches, Row, Table
from ._verdict import Bounds, Difference, Extreme, Stats, Status, Verdict, Witness

try:
    __version__ = version("celspresso")
except PackageNotFoundError:  # pragma: no cover
    __version__ = "0.0.0"

__all__ = [
    "Bounds",
    "CelError",
    "CelEvaluationError",
    "CelSubsetError",
    "CelSyntaxError",
    "CelTypeError",
    "Diagnostic",
    "Difference",
    "Env",
    "Explanation",
    "Expr",
    "Extreme",
    "Limits",
    "NoRowMatches",
    "Predicate",
    "Problem",
    "Row",
    "RuleCheck",
    "RuleSet",
    "Spec",
    "Stats",
    "Status",
    "Table",
    "Verdict",
    "VerificationFailed",
    "VerificationTimeout",
    "Witness",
    "function",
]
