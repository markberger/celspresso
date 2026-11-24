from __future__ import annotations

import typing
from collections.abc import Iterable, Mapping, Sequence
from dataclasses import dataclass, field
from types import MappingProxyType
from typing import TYPE_CHECKING, Any, ClassVar

if TYPE_CHECKING:
    from ._env import Expr, Predicate, RuleCheck

__all__ = ["Spec"]

Conditions = Mapping[str, "str | Predicate"] | Iterable["str | Predicate"]


@dataclass(frozen=True)
class Spec:
    """What a rule must satisfy, as one reusable value: pass it to `Env.check_rule`,
    `Spec.check` or `RuleSet.verify_all`.

    For a true/false rule (may this order be refunded?):

    - `invariants`: what the rule must never allow. The rule must imply each one.
    - `require`: what the rule must allow. Each case must imply the rule.

    For any rule, including one that computes a value (an amount, a label, a struct
    such as `Decision{action: 'refund', amount: ...}`):

    - `ensures`: what its result must satisfy on every valid input, as CEL over the
      inputs and `result`, e.g. `"result >= 0 && result <= order.total"`. Inputs on
      which the rule fails are left out here; failing is a problem of its own.
    - `returns`: the type the result must have (`int`, a model class, `T.fixed(10, 2)`).
    - `examples`: `(input, expected result)` pairs the rule must get right.
    - `assumptions`: facts about valid inputs that every check may rely on.

    Invariants and `ensures` keep a rule *safe*; `require` and `examples` keep it
    *useful*. Conditions are CEL strings or Predicates, given as a mapping from name to
    condition or as a list (each is then named by its source):

    >>> spec = Spec(
    ...     invariants={"capped": "order.total_cents <= 50000"},
    ...     require=["order.status == 'lost' && order.total_cents <= 10000"],
    ... )
    >>> list(spec.require)
    ["order.status == 'lost' && order.total_cents <= 10000"]
    >>> Spec(ensures={"no over-refund": "result <= order.total_cents"}, returns=int).returns
    <class 'int'>
    """

    __hash__: ClassVar[None] = None  # type: ignore[assignment]  # examples hold dicts

    invariants: Mapping[str, str | Predicate] = field(default_factory=dict)
    require: Mapping[str, str | Predicate] = field(default_factory=dict)
    ensures: Mapping[str, str | Predicate] = field(default_factory=dict)
    returns: Any = None
    examples: tuple[tuple[Mapping[str, Any], Any], ...] = ()
    assumptions: tuple[str | Predicate, ...] = ()

    def __init__(
        self,
        invariants: Conditions = (),
        *,
        require: Conditions = (),
        ensures: Conditions = (),
        returns: Any = None,
        examples: Iterable[tuple[Mapping[str, Any], Any]] = (),
        assumptions: str | Predicate | Iterable[str | Predicate] = (),
    ) -> None:
        object.__setattr__(self, "invariants", _named("invariants", invariants))
        object.__setattr__(self, "require", _named("require", require))
        object.__setattr__(self, "ensures", _named("ensures", ensures))
        object.__setattr__(self, "returns", returns)
        ex = []
        for i, item in enumerate(examples):
            # any 2-item sequence, so examples loaded from JSON (lists) work too
            ok = isinstance(item, Sequence) and not isinstance(item, str) and len(item) == 2
            if not (ok and isinstance(item[0], Mapping)):
                raise TypeError(
                    f"examples[{i}] must be an (input mapping, expected result) pair, got {item!r}"
                )
            ex.append((item[0], item[1]))
        object.__setattr__(self, "examples", tuple(ex))
        if isinstance(assumptions, str) or not isinstance(assumptions, Iterable):
            assumptions = (assumptions,)
        asm = tuple(assumptions)
        for a in asm:
            _check_condition("assumptions", a)
        object.__setattr__(self, "assumptions", asm)

    def __reduce__(self) -> tuple[Any, ...]:
        # the read-only mapping proxies can't be pickled or deep-copied; rebuild instead
        state = (dict(self.invariants), dict(self.require), dict(self.ensures), self.returns)
        return (_rebuild, (*state, self.examples, self.assumptions))

    def check(self, rule: Expr[Any], *, timeout: float | None = None) -> RuleCheck:
        """`rule.env.check_rule(rule, self)`: vet a compiled rule against this spec."""
        from ._env import Expr

        if not isinstance(rule, Expr):
            raise TypeError(
                f"Spec.check needs a compiled rule (env.compile(...)), got {rule!r}; "
                "or call env.check_rule(source, spec)"
            )
        return rule.env.check_rule(rule, self, timeout=timeout)

    def assuming(self, *conditions: str | Predicate) -> Spec:
        """A copy of this spec with more assumptions."""
        return Spec(
            self.invariants,
            require=self.require,
            ensures=self.ensures,
            returns=self.returns,
            examples=self.examples,
            assumptions=(*self.assumptions, *conditions),
        )


def _rebuild(
    invariants: dict[str, Any],
    require: dict[str, Any],
    ensures: dict[str, Any],
    returns: Any,
    examples: Any,
    assumptions: Any,
) -> Spec:
    return Spec(
        invariants,
        require=require,
        ensures=ensures,
        returns=returns,
        examples=examples,
        assumptions=assumptions,
    )


def _check_condition(where: str, c: Any) -> None:
    from ._env import Predicate

    if not isinstance(c, (str, Predicate)):
        raise TypeError(f"Spec {where}: expected a CEL condition (str or Predicate), got {c!r}")


def _named(where: str, items: Conditions) -> Mapping[str, str | Predicate]:
    """Name each condition: by its key, or by its source."""
    if isinstance(items, (str, bytes)):
        raise TypeError(f"Spec {where}: pass a list or a mapping of conditions, not a single string")
    if isinstance(items, Mapping):
        out = dict(typing.cast("Mapping[str, str | Predicate]", items))
    else:
        out = {i if isinstance(i, str) else getattr(i, "source", repr(i)): i for i in items}
    for c in out.values():
        _check_condition(where, c)
    return MappingProxyType(out)  # read-only: a Spec is a value
