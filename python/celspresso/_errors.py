from __future__ import annotations

from dataclasses import dataclass
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from ._verdict import Bounds, Verdict

__all__ = [
    "CelError",
    "CelEvaluationError",
    "CelSubsetError",
    "CelSyntaxError",
    "CelTypeError",
    "Diagnostic",
    "VerificationFailed",
    "VerificationTimeout",
]


@dataclass(frozen=True)
class Diagnostic:
    """One problem in a CEL source, with a character span.

    `code` says what kind of problem it is: "syntax" (doesn't parse), "type" (doesn't
    type-check: an unknown field, a wrong argument), "subset" (valid CEL, but outside
    celspresso's subset; the message says what to write instead) or "lint" (a warning
    from `Expr.warnings`)."""

    message: str
    start: int
    end: int
    rendered: str
    code: str = "type"

    def __str__(self) -> str:
        return self.rendered


class CelError(Exception):
    """Base class for every celspresso error."""


class _CompileFailure(CelError):
    def __init__(self, source: str, diagnostics: list[Diagnostic]):
        self.source = source
        self.diagnostics = diagnostics
        super().__init__(self._format())

    @property
    def span(self) -> tuple[int, int]:
        d = self.diagnostics[0]
        return (d.start, d.end)

    @property
    def message(self) -> str:
        return self.diagnostics[0].message

    def _format(self) -> str:
        # each rendered diagnostic starts with "line:col: message", so the first line of
        # the error is the first problem itself
        return "\n".join(d.rendered for d in self.diagnostics)


class CelSyntaxError(_CompileFailure):
    """The expression does not parse."""


class CelTypeError(_CompileFailure):
    """The expression parses but does not type-check against the environment."""


class CelSubsetError(CelTypeError):
    """The expression is valid CEL but uses something outside celspresso's subset (the
    part the verifier decides exactly and quickly). Each message says what to write
    instead. A subclass of CelTypeError, so code catching that still catches this."""


class CelEvaluationError(CelError):
    """Evaluation failed (division by zero, missing key, overflow, ...).

    Messages never contain runtime values, so they are safe to log.
    """

    def __init__(self, message: str, expression_id: int, span: tuple[int, int], rendered: str):
        self.message = message
        self.expression_id = expression_id
        self.span = span
        self.rendered = rendered
        super().__init__(rendered)


class VerificationFailed(CelError, AssertionError):
    """Raised by `Verdict.expect()` when a property does not hold."""

    def __init__(self, verdict: Verdict | Bounds, message: str):
        self.verdict = verdict
        super().__init__(message)


class VerificationTimeout(VerificationFailed):
    """The solver ran out of time; the property is neither proved nor refuted."""
