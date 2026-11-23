from __future__ import annotations

import datetime as _dt
import enum
from collections.abc import Iterator, Mapping, Sequence
from dataclasses import dataclass, field
from typing import Any, NoReturn

from ._errors import VerificationFailed, VerificationTimeout
from ._types import SchemaBuilder, TypeSpec, from_cel

__all__ = ["Bounds", "Difference", "Extreme", "Stats", "Status", "Verdict", "Witness"]


class Status(enum.Enum):
    """The answer to a verification question, always about the property that was asked:
    PROVED means it holds (for `satisfiable()`: some input makes it true), REFUTED means
    it doesn't, UNKNOWN means the solver couldn't decide."""

    PROVED = "proved"
    REFUTED = "refuted"
    UNKNOWN = "unknown"

    def __repr__(self) -> str:
        return f"Status.{self.name}"


class Witness(Mapping[str, Any]):
    """Concrete input found by the solver (already replayed through the evaluator).

    Values are raw CEL data (structs as dicts); `to_python()` rebuilds your models.
    To replay it, pass the Witness itself to `evaluate`/`explain`: that skips field
    readers, which expect your host objects, not this data.
    """

    def __init__(
        self,
        raw: Mapping[str, Any],
        specs: Mapping[str, TypeSpec],
        schema: SchemaBuilder,
        paths: Sequence[str] = (),
    ):
        self._raw = dict(raw)
        self._specs = specs
        self._schema = schema
        self._paths = tuple(paths)

    def __getitem__(self, key: str) -> Any:
        return self._raw[key]

    def __iter__(self) -> Iterator[str]:
        return iter(self._raw)

    def __len__(self) -> int:
        return len(self._raw)

    def to_python(self) -> dict[str, Any]:
        """Convert to Python objects; Pydantic models go through `model_validate`."""
        return {k: from_cel(v, self._specs.get(k, "dyn"), self._schema) for k, v in self._raw.items()}

    @property
    def relevant(self) -> dict[str, Any]:
        """Only the values the question's expressions read, by path:
        `{'p.status': 'provisional', 'today': date(2026, 11, 21)}`. Everything else in the
        witness is arbitrary filler the solver had to pick."""
        leaves = [p for p in self._paths if not any(q.startswith(p + ".") for q in self._paths)]
        out: dict[str, Any] = {}
        for path in leaves:
            ok, value = lookup(self._raw, path)
            if ok:
                out[path] = value
        return out or dict(self._raw)

    def __str__(self) -> str:
        """The relevant values as CEL-style assignments, for people and LLMs."""
        return ", ".join(f"{k} = {_show(v)}" for k, v in self.relevant.items())

    def __repr__(self) -> str:
        return f"Witness({self._raw!r})"


def lookup(w: Mapping[str, Any], path: str) -> tuple[bool, Any]:
    head, *rest = path.split(".")
    if head not in w:
        return False, None
    cur = w[head]
    for part in rest:
        if not isinstance(cur, Mapping) or part not in cur:
            return False, None
        cur = cur[part]
    return True, cur


def _show(v: Any) -> str:
    if isinstance(v, (_dt.date, _dt.datetime)):
        return v.isoformat()
    if isinstance(v, bool):
        return "true" if v else "false"
    if v is None:
        return "null"
    return repr(v)


@dataclass(frozen=True)
class Stats:
    elapsed_ms: float
    approximations: tuple[str, ...] = ()


@dataclass(frozen=True)
class Extreme:
    """One end of an expression's range."""

    value: Any
    witness: Witness
    #: the witness replays through the evaluator to exactly `value`
    attained: bool
    #: no valid input gives a value beyond this one (proved by an unsatisfiable check)
    sound: bool


@dataclass(frozen=True)
class Bounds:
    """The range of a numeric expression over every valid input on which it does not error.

    `proved` means both ends are exact: sound (nothing lies beyond) and attained (the
    witness really evaluates to it). Otherwise `reason` says what is missing.
    """

    question: str
    min: Extreme | None
    max: Extreme | None
    reason: str | None = None
    bounded: bool = False
    assumptions: tuple[str, ...] = ()
    stats: Stats = field(default_factory=lambda: Stats(0.0))

    @property
    def proved(self) -> bool:
        return all(x is not None and x.sound and x.attained for x in (self.min, self.max))

    def expect(self) -> tuple[Any, Any]:
        """`(min, max)` if both ends are proved, otherwise raise VerificationFailed."""
        if not self.proved or self.min is None or self.max is None:
            raise VerificationFailed(self, f"{self.question}: not proved ({self.reason or 'unknown'})")
        return self.min.value, self.max.value

    def __bool__(self) -> NoReturn:
        raise TypeError("Bounds has no truth value; use .proved or .expect()")

    def __str__(self) -> str:
        def end(x: Extreme | None) -> str:
            return "?" if x is None else _show(x.value) + ("" if x.sound and x.attained else "?")

        tail = "" if self.proved else f" (not proved: {self.reason})"
        return f"[{end(self.min)}, {end(self.max)}]{tail}"


@dataclass(frozen=True)
class Difference:
    """One input on which two expressions disagree, and what each gives for it.

    `before` and `after` are the values of the first and second expression, or a
    `CelEvaluationError` when that one fails on this input."""

    witness: Witness
    before: Any
    after: Any

    def __str__(self) -> str:
        return f"when {self.witness}: {_outcome(self.before)} -> {_outcome(self.after)}"


def _outcome(v: Any) -> str:
    from ._errors import CelEvaluationError

    if isinstance(v, CelEvaluationError):
        return f"error ({v.message})"
    return _show(v)


@dataclass(frozen=True)
class Verdict:
    """The outcome of a verification question.

    The status is always about the property asked: `x.never_errors().proved` means x
    can't fail, `p.satisfiable().proved` means some input makes p true. `witness` is the
    evidence: an example input when a `satisfiable()` question is PROVED, a
    counterexample when any other question is REFUTED.

    Verdicts deliberately refuse `bool()`: an UNKNOWN must never be mistaken for a
    yes or a no. Use `.proved`, `.refuted`, `.unknown` or `.expect()`.
    """

    status: Status
    question: str
    witness: Witness | None = None
    reason: str | None = None
    bounded: bool = False
    assumptions: tuple[str, ...] = ()
    stats: Stats = field(default_factory=lambda: Stats(0.0))

    # -- status helpers ---------------------------------------------------
    @property
    def proved(self) -> bool:
        return self.status is Status.PROVED

    @property
    def refuted(self) -> bool:
        return self.status is Status.REFUTED

    @property
    def unknown(self) -> bool:
        return self.status is Status.UNKNOWN

    @property
    def counterexample(self) -> Witness | None:
        """The input that refutes the property, when it is REFUTED."""
        return self.witness if self.status is Status.REFUTED else None

    @property
    def example(self) -> Witness | None:
        """An input for which the property holds, when a PROVED answer comes with one
        (`satisfiable()`)."""
        return self.witness if self.status is Status.PROVED else None

    def __bool__(self) -> NoReturn:
        raise TypeError(
            "a Verdict has no truth value (it may be UNKNOWN); "
            "use .proved / .refuted / .unknown, or .expect()"
        )

    def expect(self) -> Verdict:
        """Return self if the property is PROVED; raise otherwise."""
        if self.status is Status.PROVED:
            return self
        if self.status is Status.UNKNOWN and self.reason and "timeout" in self.reason:
            raise VerificationTimeout(self, self._explain())
        raise VerificationFailed(self, self._explain())

    def _explain(self) -> str:
        lines = [f"{self.question}: {self.status.name}"]
        if self.witness is not None:
            label = "counterexample" if self.status is Status.REFUTED else "example"
            lines.append(f"  {label}:")
            for k, v in self.witness.relevant.items():
                lines.append(f"    {k} = {_show(v)}")
        if self.reason:
            lines.append(f"  reason: {self.reason}")
        if self.bounded:
            lines.append("  (result relied on the unroll limit)")
        if self.assumptions:
            lines.append("  assuming: " + " && ".join(f"({a})" for a in self.assumptions))
        return "\n".join(lines)

    def __str__(self) -> str:
        return self._explain()

    def __repr__(self) -> str:
        parts = [self.status.name]
        if self.witness is not None:
            parts.append(f"{'counterexample' if self.refuted else 'example'}={dict(self.witness)!r}")
        if self.reason:
            parts.append(f"reason={self.reason!r}")
        if self.bounded:
            parts.append("bounded=True")
        return f"Verdict({', '.join(parts)})"

    def _repr_markdown_(self) -> str:
        return "```\n" + self._explain() + "\n```"
