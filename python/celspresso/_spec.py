from __future__ import annotations

import typing
from collections.abc import Iterable, Mapping
from dataclasses import dataclass, field
from typing import TYPE_CHECKING, Any

if TYPE_CHECKING:
    from ._env import Predicate, RuleCheck

__all__ = ["Spec"]

Conditions = Mapping[str, "str | Predicate"] | Iterable["str | Predicate"]


@dataclass(frozen=True)
class Spec:
    """What a rule must satisfy, as one reusable value: pass it to `Env.check_rule`,
    `Spec.check` or `RuleSet.verify_all`.

    - `invariants`: what the rule must never allow. The rule must imply each one.
    - `require`: what the rule must allow. Each case must imply the rule.
    - `examples`: `(input, expected answer)` pairs the rule must get right.
    - `assumptions`: facts about valid inputs that every check may rely on.

    Invariants keep a rule *safe*; `require` and `examples` keep it *useful*. Conditions
    are CEL strings or Predicates, given as a mapping from name to condition or as a
    list (each is then named by its source):

    >>> spec = Spec(
    ...     invariants={"capped": "order.total_cents <= 50000"},
    ...     require=["order.status == 'lost' && order.total_cents <= 10000"],
    ... )
    >>> list(spec.require)
    ["order.status == 'lost' && order.total_cents <= 10000"]
    """

    invariants: Mapping[str, str | Predicate] = field(default_factory=dict)
    require: Mapping[str, str | Predicate] = field(default_factory=dict)
    examples: tuple[tuple[Mapping[str, Any], bool], ...] = ()
    assumptions: tuple[str | Predicate, ...] = ()

    def __init__(
        self,
        invariants: Conditions = (),
        *,
        require: Conditions = (),
        examples: Iterable[tuple[Mapping[str, Any], bool]] = (),
        assumptions: str | Predicate | Iterable[str | Predicate] = (),
    ) -> None:
        object.__setattr__(self, "invariants", _named("invariants", invariants))
        object.__setattr__(self, "require", _named("require", require))
        ex = tuple(examples)
        for i, item in enumerate(ex):
            if not (isinstance(item, tuple) and len(item) == 2 and isinstance(item[1], bool)):
                raise TypeError(f"examples[{i}] must be an (input, expected bool) pair, got {item!r}")
        object.__setattr__(self, "examples", ex)
        if isinstance(assumptions, str) or not isinstance(assumptions, Iterable):
            assumptions = (assumptions,)
        asm = tuple(assumptions)
        for a in asm:
            _check_condition("assumptions", a)
        object.__setattr__(self, "assumptions", asm)

    def check(self, rule: Predicate, *, timeout: float | None = None) -> RuleCheck:
        """`rule.env.check_rule(rule, self)`: vet a compiled rule against this spec."""
        return rule.env.check_rule(rule, self, timeout=timeout)

    def assuming(self, *conditions: str | Predicate) -> Spec:
        """A copy of this spec with more assumptions."""
        return Spec(
            self.invariants,
            require=self.require,
            examples=self.examples,
            assumptions=(*self.assumptions, *conditions),
        )


def _check_condition(where: str, c: Any) -> None:
    from ._env import Predicate

    if not isinstance(c, (str, Predicate)):
        raise TypeError(f"Spec {where}: expected a CEL condition (str or Predicate), got {c!r}")


def _named(where: str, items: Conditions) -> dict[str, str | Predicate]:
    """Name each condition: by its key, or by its source."""
    if isinstance(items, (str, bytes)):
        raise TypeError(f"Spec {where}: pass a list or a mapping of conditions, not a single string")
    if isinstance(items, Mapping):
        out = dict(typing.cast("Mapping[str, str | Predicate]", items))
    else:
        out = {i if isinstance(i, str) else getattr(i, "source", repr(i)): i for i in items}
    for c in out.values():
        _check_condition(where, c)
    return out
