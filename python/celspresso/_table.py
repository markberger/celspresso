"""Decision tables: rows of `when -> then`, the first matching row giving the result."""

from __future__ import annotations

from collections.abc import Iterable, Mapping, Sequence
from dataclasses import dataclass
from itertools import combinations
from typing import TYPE_CHECKING, Any

from ._env import Problem, RuleCheck
from ._errors import CelError
from ._spec import Spec

if TYPE_CHECKING:
    from ._env import Env, Expr, Predicate
    from ._verdict import Verdict


@dataclass(frozen=True)
class Row:
    """One row of a `Table`: when `when` holds (and no earlier row does), the table
    gives `then`. `name` labels it in reports (default: `row 1`, `row 2`, ...)."""

    when: str
    then: str
    name: str | None = None


class NoRowMatches(LookupError):
    """`Table.evaluate` was given an input that no row matches (and there's no default)."""


class Table:
    """A first-match decision table, built with `Env.decision_table`.

    It is one CEL expression (`source`, `expr`), so everything that works on a rule
    works on it: `check` vets it against a `Spec` like `Env.check_rule`, and also
    checks the table itself: every input matches some row (unless there's a default),
    every row can be the first match for some input, and, with `unique=True`, no two
    rows match the same input.
    """

    def __init__(
        self,
        env: Env,
        rows: Sequence[Row | tuple[str, str]] | Mapping[str, tuple[str, str]],
        default: str | None = None,
        *,
        unique: bool = False,
    ) -> None:
        self.env = env
        self.rows = _rows(rows)
        if not self.rows:
            raise ValueError("a table needs at least one row")
        names = [r.name for r in self.rows]
        if len(set(names)) != len(names):
            raise ValueError(f"row names must be distinct: {names}")
        self.default = default
        self.unique = unique
        self.source = _source(self.rows, default)
        self._expr: Expr[Any] | None = None

    def __repr__(self) -> str:
        return f"Table({len(self.rows)} rows{', default' if self.default is not None else ''})"

    @property
    def expr(self) -> Expr[Any]:
        """The whole table as one compiled expression. With no default, an input that
        no row matches makes it fail (an index-out-of-range error)."""
        if self._expr is None:
            self._expr = self.env.compile(self.source)
        return self._expr

    def evaluate(self, data: Mapping[str, Any]) -> Any:
        """The `then` of the first row whose `when` holds on `data`, else the default.
        Raises NoRowMatches when nothing matches and there's no default."""
        for row in self.rows:
            if self.env.predicate(row.when).evaluate(data):
                return self.env.compile(row.then).evaluate(data)
        if self.default is None:
            raise NoRowMatches("no row of the table matches this input")
        return self.env.compile(self.default).evaluate(data)

    def matching_row(self, data: Mapping[str, Any]) -> str | None:
        """The name of the row that decides `data` (None: no row, so the default)."""
        for row in self.rows:
            if self.env.predicate(row.when).evaluate(data):
                return row.name
        return None

    def check(
        self,
        spec: Spec | Mapping[str, str | Predicate] | Iterable[str | Predicate] = (),
        *,
        timeout: float | None = None,
    ) -> RuleCheck:
        """Vet the table: its structure (see the class), then the whole table as a rule
        with `Env.check_rule`. Problems name the row they concern."""
        spec = spec if isinstance(spec, Spec) else Spec(spec)
        assuming = spec.assumptions
        try:
            whens = [self.env.predicate(r.when) for r in self.rows]
        except CelError as e:
            return RuleCheck(self.source, None, (Problem("invalid", f"a row's condition: {e}"),))
        try:  # every result has one type (and the spec's, if it names one)
            self.expr  # noqa: B018
        except CelError as e:
            return RuleCheck(self.source, None, (Problem("invalid", str(e)),))
        problems: list[Problem] = []

        def undecided(what: str, v: Verdict) -> None:
            problems.append(Problem("unverified", f"could not decide whether {what}: {v.reason}", None, v))

        any_row = _any(whens)
        for i, (row, w) in enumerate(zip(self.rows, whens, strict=True)):
            first = w if i == 0 else self.env.predicate(f"{_wrap(w.source)} && !({_any(whens[:i])})")
            v = first.satisfiable(assuming=assuming, timeout=timeout)
            if v.unknown:
                undecided(f"{row.name} can match", v)
            elif v.refuted:
                alone = i > 0 and w.satisfiable(assuming=assuming, timeout=timeout).proved
                why = f": {_names(self.rows[:i])} catch every input it matches" if alone else ""
                problems.append(Problem("shadowed", f"{row.name} never decides anything{why}", None, v))
        gap = self.env.predicate(f"!(\n{any_row}\n)").satisfiable(assuming=assuming, timeout=timeout)
        if gap.unknown:
            undecided("every input matches a row", gap)
        elif gap.proved and self.default is None:
            problems.append(Problem("no_match", f"no row matches {_when(gap)}", None, gap))
        elif gap.refuted and self.default is not None:
            problems.append(
                Problem("shadowed", "the default is never used: the rows cover every input", None, gap)
            )
        if self.unique:
            for (a, wa), (b, wb) in combinations(zip(self.rows, whens, strict=True), 2):
                v = self.env.predicate(f"{_wrap(wa.source)} && {_wrap(wb.source)}").satisfiable(
                    assuming=assuming, timeout=timeout
                )
                if v.unknown:
                    undecided(f"{a.name} and {b.name} overlap", v)
                elif v.proved:
                    problems.append(
                        Problem("overlap", f"{a.name} and {b.name} both match {_when(v)}", None, v)
                    )
        # the table as one rule; without a default, inputs no row matches were reported
        # above, and only fail, so the rule's own checks are over the inputs some row takes
        whole = spec if self.default is not None else spec.assuming(any_row)
        rule = self.env.check_rule(self.source, whole, timeout=timeout)
        problems += [self._attribute(p) for p in rule.problems]
        return RuleCheck(self.source, rule.rule, tuple(problems))

    def _attribute(self, p: Problem) -> Problem:
        """`p`, naming the row that decides its counterexample."""
        w = p.verdict.witness if p.verdict is not None else None
        if w is None:
            return p
        try:
            name = self.matching_row(w)
        except Exception:  # noqa: BLE001 - a nicety; the witness is the evidence
            return p
        where = name if name is not None else "the default"
        return Problem(p.kind, f"{where}: {p.message}", p.invariant, p.verdict)


def _rows(rows: Sequence[Row | tuple[str, str]] | Mapping[str, tuple[str, str]]) -> tuple[Row, ...]:
    items: Iterable[Row | tuple[str, str]] = (
        [Row(*_pair(v), name=str(k)) for k, v in rows.items()] if isinstance(rows, Mapping) else rows
    )
    out = []
    for i, r in enumerate(items, 1):
        row = r if isinstance(r, Row) else Row(*_pair(r))
        out.append(row if row.name is not None else Row(row.when, row.then, f"row {i}"))
    return tuple(out)


def _pair(v: Any) -> tuple[str, str]:
    if isinstance(v, tuple) and len(v) == 2 and all(isinstance(x, str) for x in v):
        return v
    raise TypeError(f"a table row is Row(when, then) or a (when, then) pair of CEL strings, got {v!r}")


def _wrap(src: str) -> str:
    # on lines of its own if it has a comment or spans lines, so a `//` can't swallow code
    return f"(\n{src}\n)" if "//" in src or "\n" in src else f"({src})"


def _source(rows: Sequence[Row], default: str | None) -> str:
    """`w1 ? t1 : w2 ? t2 : ... : default`. With no default, the last branch indexes past
    the end of a one-element list of the last row's result: an error of the right type."""
    branches = [f"{_wrap(r.when)} ? {_wrap(r.then)} :" for r in rows]
    tail = _wrap(default) if default is not None else f"// no row matches\n[{_wrap(rows[-1].then)}][1]"
    return "\n".join([*branches, tail])


def _any(whens: Sequence[Predicate]) -> str:
    return " || ".join(_wrap(w.source) for w in whens)


def _when(v: Verdict) -> str:
    """'when <the satisfying input>', or 'on every input' when it reads no input."""
    shown = str(v.witness or "")
    return f"when {shown}" if shown else "on every input"


def _names(rows: Sequence[Row]) -> str:
    names = [r.name or "" for r in rows]
    return names[0] if len(names) == 1 else ", ".join(names[:-1]) + " and " + names[-1]
