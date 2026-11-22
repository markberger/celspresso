from __future__ import annotations

import datetime as _dt
import enum
from collections.abc import Iterator, Mapping, Sequence
from dataclasses import dataclass, field
from typing import Any, NoReturn

from ._errors import VerificationFailed, VerificationTimeout
from ._types import SchemaBuilder, TypeSpec, from_cel

__all__ = ["Stats", "Status", "Verdict", "Witness"]


class Status(enum.Enum):
    SAT = "sat"
    UNSAT = "unsat"
    PROVED = "proved"
    REFUTED = "refuted"
    UNKNOWN = "unknown"

    def __repr__(self) -> str:
        return f"Status.{self.name}"


class Witness(Mapping[str, Any]):
    """Concrete input found by the solver (already replayed through the evaluator).

    Values are raw CEL data (structs as dicts); `to_python()` rebuilds your models.
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
class Verdict:
    """The outcome of a verification query.

    Verdicts deliberately refuse `bool()`: an UNKNOWN must never be mistaken for a
    yes or a no. Use `.proved`, `.refuted`, `.sat`, `.unsat`, `.unknown` or `.expect()`.
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
    def sat(self) -> bool:
        return self.status is Status.SAT

    @property
    def unsat(self) -> bool:
        return self.status is Status.UNSAT

    @property
    def unknown(self) -> bool:
        return self.status is Status.UNKNOWN

    @property
    def counterexample(self) -> Witness | None:
        return self.witness if self.status is Status.REFUTED else None

    def __bool__(self) -> NoReturn:
        raise TypeError(
            "a Verdict has no truth value (it may be UNKNOWN); "
            "use .proved / .refuted / .sat / .unsat / .unknown, or .expect()"
        )

    def expect(self) -> Verdict:
        """Return self if the property holds (PROVED or SAT); raise otherwise."""
        if self.status in (Status.PROVED, Status.SAT):
            return self
        if self.status is Status.UNKNOWN and self.reason and "timeout" in self.reason:
            raise VerificationTimeout(self, self._explain())
        raise VerificationFailed(self, self._explain())

    def _explain(self) -> str:
        lines = [f"{self.question}: {self.status.name}"]
        if self.witness is not None:
            label = "counterexample" if self.status is Status.REFUTED else "witness"
            lines.append(f"  {label}:")
            for k, v in self.witness.relevant.items():
                lines.append(f"    {k} = {_show(v)}")
        if self.reason:
            lines.append(f"  reason: {self.reason}")
        if self.bounded:
            lines.append("  (result relied on the comprehension unroll limit)")
        if self.assumptions:
            lines.append("  assuming: " + " && ".join(f"({a})" for a in self.assumptions))
        return "\n".join(lines)

    def __str__(self) -> str:
        return self._explain()

    def __repr__(self) -> str:
        parts = [self.status.name]
        if self.witness is not None:
            parts.append(f"{'counterexample' if self.refuted else 'witness'}={dict(self.witness)!r}")
        if self.reason:
            parts.append(f"reason={self.reason!r}")
        if self.bounded:
            parts.append("bounded=True")
        return f"Verdict({', '.join(parts)})"

    def _repr_markdown_(self) -> str:
        return "```\n" + self._explain() + "\n```"
