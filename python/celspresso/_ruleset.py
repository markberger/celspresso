from __future__ import annotations

from itertools import combinations
from typing import TYPE_CHECKING, Any

from ._env import Expr, Predicate
from ._spec import Spec

if TYPE_CHECKING:
    from collections.abc import Callable, Iterable, Mapping

    from ._env import RuleCheck
    from ._verdict import Difference, Verdict

__all__ = ["RuleSet"]


class RuleSet:
    """A named collection of expressions from one Env, checked as a group."""

    def __init__(self, rules: Mapping[str, Expr[Any]], *, assumptions: Iterable[str | Predicate] = ()):
        if not rules:
            raise ValueError("a RuleSet needs at least one rule")
        envs = {r.env._fingerprint for r in rules.values()}
        if len(envs) != 1:
            raise ValueError("all rules in a RuleSet must come from the same Env")
        self.rules: dict[str, Expr[Any]] = dict(rules)
        self.assumptions = tuple(a if isinstance(a, str) else a.source for a in assumptions)

    def __getitem__(self, name: str) -> Expr[Any]:
        return self.rules[name]

    def __iter__(self):
        return iter(self.rules)

    def __len__(self) -> int:
        return len(self.rules)

    def evaluate(self, data: Mapping[str, Any]) -> dict[str, Any]:
        return {n: r.evaluate(data) for n, r in self.rules.items()}

    def unreachable(self, *, timeout: float | None = None) -> dict[str, Verdict]:
        """Predicates that can never be true (REFUTED) or could not be decided (UNKNOWN)."""
        out = {}
        for n, r in self.rules.items():
            if isinstance(r, Predicate):
                v = r.satisfiable(assuming=self.assumptions, timeout=timeout)
                if not v.proved:
                    out[n] = v
        return out

    def may_error(self, *, timeout: float | None = None) -> dict[str, Verdict]:
        """Rules that some valid input makes fail (REFUTED `never_errors()`), or for which
        that could not be decided (UNKNOWN)."""
        out = {}
        for n, r in self.rules.items():
            v = r.never_errors(assuming=self.assumptions, timeout=timeout)
            if not v.proved:
                out[n] = v
        return out

    def verify_all(
        self,
        spec: Spec | Mapping[str, str | Predicate] | Iterable[str | Predicate] = (),
        *,
        timeout: float | None = None,
    ) -> dict[str, RuleCheck]:
        """`Env.check_rule` on every predicate, against a `Spec` (or just invariants), under
        the set's assumptions too. `all(c.ok for c in rs.verify_all(spec).values())` means
        the whole set is proved to meet it."""
        spec = (spec if isinstance(spec, Spec) else Spec(spec)).assuming(*self.assumptions)
        out = {}
        for n, r in self.rules.items():
            if isinstance(r, Predicate):
                out[n] = r.env.check_rule(r, spec, timeout=timeout)
        return out

    def check_pairwise(
        self, check: Callable[[Predicate, Predicate], Verdict], *, symmetric: bool = True
    ) -> dict[tuple[str, str], Verdict]:
        """Apply `check(a, b)` to every pair of predicates.

        Example: find overlapping rules with
        `rs.check_pairwise(lambda a, b: (a & b).satisfiable())`.
        """
        preds = [(n, r) for n, r in self.rules.items() if isinstance(r, Predicate)]
        pairs = (
            combinations(preds, 2) if symmetric else ((x, y) for x in preds for y in preds if x[0] != y[0])
        )
        return {(a[0], b[0]): check(a[1], b[1]) for a, b in pairs}

    def diff(
        self, other: RuleSet, *, limit: int = 5, timeout: float | None = None
    ) -> dict[str, list[Difference]]:
        """For each rule name in both sets, inputs on which old and new disagree (under
        this set's assumptions)."""
        out = {}
        for n, old in self.rules.items():
            new = other.rules.get(n)
            if new is None:
                continue
            ws = old.diff(new, limit=limit, assuming=self.assumptions, timeout=timeout)
            if ws:
                out[n] = ws
        return out
