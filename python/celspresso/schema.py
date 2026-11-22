"""Declare CEL types directly, without Python classes.

Python annotations (`int`, `list[str]`, a Pydantic model) are the convenient way to
describe data; this module is the exact way, for integrations that have their own
type systems (ORM models, historical migration states, JSON Schema) or no classes at
all. Everything here is a frozen value, and accepted anywhere an annotation is:

>>> from celspresso import Env
>>> from celspresso.schema import T, Field, Struct, Constraints
>>> order = Struct(
...     "shop.Order",
...     [
...         Field("total", T.int, Constraints(ge=0)),
...         Field("note", T.nullable(T.string), Constraints(max_length=200)),
...     ],
... )
>>> env = Env(structs=[order], order=T.struct("shop.Order"))
>>> env.predicate("order.total < 0").satisfiable().unsat
True

Values of a declared struct are read from mappings or attributes and come back from
the verifier as plain dicts.
"""

from __future__ import annotations

import math
import re
from dataclasses import dataclass, field
from typing import TYPE_CHECKING, Any

if TYPE_CHECKING:
    from collections.abc import Iterable

    from ._types import TypeSpec

__all__ = ["Constraints", "Field", "Struct", "T", "TypeRef"]

_SCALARS = (
    "bool",
    "int",
    "uint",
    "double",
    "string",
    "bytes",
    "date",
    "timestamp",
    "duration",
    "null",
    "dyn",
)
# names CEL's checker or our type display already use
_RESERVED = {*_SCALARS, "list", "map", "type", "null_type", "optional_type", "any"}
# dotted identifiers, optionally versioned: `shop.Order`, `Patient@2`
_STRUCT_NAME = re.compile(r"[A-Za-z_]\w*(\.[A-Za-z_]\w*)*([@#][A-Za-z0-9_.]+)?")


class TypeRef:
    """A CEL type. Build them with `T`: `T.int`, `T.list(T.string)`, `T.struct("Order")`.

    TypeRefs are immutable and hashable, and compare equal when they denote the same
    type. Their representation is private."""

    __slots__ = ("_spec",)
    _spec: TypeSpec

    def __init__(self, spec: TypeSpec) -> None:
        _check_spec(spec)
        object.__setattr__(self, "_spec", spec)

    def __setattr__(self, name: str, value: Any) -> None:
        raise AttributeError("TypeRef is immutable")

    def __eq__(self, other: object) -> bool:
        return isinstance(other, TypeRef) and self._spec == other._spec

    def __hash__(self) -> int:
        return hash(self._spec)

    def __str__(self) -> str:
        from ._types import type_name  # _types imports this module

        return type_name(self._spec)

    def __repr__(self) -> str:
        return f"TypeRef({self})"

    def __reduce__(self) -> tuple[Any, ...]:
        return (TypeRef._unchecked, (self._spec,))

    @classmethod
    def _unchecked(cls, spec: TypeSpec) -> TypeRef:
        # for specs celspresso built itself (adapter struct names may be any string)
        ref = cls.__new__(cls)
        object.__setattr__(ref, "_spec", spec)
        return ref


def _check_spec(spec: Any) -> None:
    if isinstance(spec, str) and spec in _SCALARS:
        return
    if isinstance(spec, tuple) and spec:
        kind, args = spec[0], spec[1:]
        if kind == "struct" and len(args) == 1:
            _check_struct_name(args[0])
            return
        if (kind, len(args)) in {("list", 1), ("nullable", 1), ("map", 2)}:
            for a in args:
                _check_spec(a)
            return
    raise TypeError(f"not a CEL type: {spec!r}; build types with celspresso.schema.T")


def _check_struct_name(name: Any) -> None:
    if not isinstance(name, str) or not _STRUCT_NAME.fullmatch(name) or name in _RESERVED:
        raise ValueError(
            f"invalid struct name {name!r}: use a dotted identifier such as 'shop.Order' "
            "(optionally versioned, 'Patient@2') that is not a CEL type name"
        )


class T:
    """The CEL types, as `TypeRef` values."""

    bool = TypeRef("bool")
    int = TypeRef("int")
    uint = TypeRef("uint")
    double = TypeRef("double")
    string = TypeRef("string")
    bytes = TypeRef("bytes")
    date = TypeRef("date")
    timestamp = TypeRef("timestamp")
    duration = TypeRef("duration")
    null = TypeRef("null")
    dyn = TypeRef("dyn")

    @staticmethod
    def list(elem: TypeRef) -> TypeRef:
        return TypeRef(("list", _ref(elem, "T.list")._spec))

    @staticmethod
    def map(key: TypeRef, value: TypeRef) -> TypeRef:
        return TypeRef(("map", _ref(key, "T.map key")._spec, _ref(value, "T.map value")._spec))

    @staticmethod
    def nullable(inner: TypeRef) -> TypeRef:
        """A value that may be null (Python's `Optional[...]`)."""
        spec = _ref(inner, "T.nullable")._spec
        return TypeRef(spec if isinstance(spec, tuple) and spec[0] == "nullable" else ("nullable", spec))

    @staticmethod
    def struct(name: str) -> TypeRef:
        """A struct declared with `Struct(name, ...)` in the same Env. (Refer to a Python
        class with the class itself, not by name: its CEL name is assigned for it.)"""
        return TypeRef(("struct", name))


def _ref(t: Any, where: str) -> TypeRef:
    if not isinstance(t, TypeRef):
        raise TypeError(f"{where}: expected a TypeRef (such as T.int), got {t!r}")
    return t


@dataclass(frozen=True)
class Constraints:
    """Facts about a field's values. The verifier assumes them; `evaluate` enforces them.

    Bounds apply to numbers, lengths to strings (in characters), bytes, lists and maps,
    `pattern` (an unanchored regex) to strings, `one_of` to strings and ints, and
    `items` to each element of a list. Declaring a struct checks each constraint
    against its field's type.
    """

    ge: float | None = None
    gt: float | None = None
    le: float | None = None
    lt: float | None = None
    min_length: int | None = None
    max_length: int | None = None
    pattern: str | None = None
    one_of: tuple[Any, ...] | None = None
    items: Constraints | None = None

    def __post_init__(self) -> None:
        for key in ("ge", "gt", "le", "lt"):
            v = getattr(self, key)
            if v is None:
                continue
            if isinstance(v, bool) or not isinstance(v, (int, float)):
                raise TypeError(f"Constraints({key}=...) must be a number, got {v!r}")
            if not math.isfinite(v):
                raise ValueError(f"Constraints({key}=...) must be finite, got {v!r}")
            if isinstance(v, int) and float(v) != v:
                # bounds are solved and checked as doubles; never round one silently
                raise ValueError(f"Constraints({key}={v}) is not exactly representable as a double")
        for key in ("min_length", "max_length"):
            v = getattr(self, key)
            if v is not None and (isinstance(v, bool) or not isinstance(v, int) or v < 0):
                raise TypeError(f"Constraints({key}=...) must be a non-negative int, got {v!r}")
        if self.pattern is not None and not isinstance(self.pattern, str):
            raise TypeError(f"Constraints(pattern=...) must be a str, got {self.pattern!r}")
        if self.one_of is not None:
            if not isinstance(self.one_of, (list, tuple)):
                raise TypeError(f"Constraints(one_of=...) must be a list or tuple, got {self.one_of!r}")
            values = tuple(self.one_of)
            kinds = {type(v) for v in values}
            if not values or not (kinds == {str} or kinds == {int}):
                raise TypeError(
                    "Constraints(one_of=...) must be a non-empty list of all-str or all-int values"
                )
            if kinds == {int} and not all(-(2**63) <= v < 2**64 for v in values):
                raise ValueError("Constraints(one_of=...) ints must fit in int64 or uint64")
            object.__setattr__(self, "one_of", values)
        if self.items is not None and not isinstance(self.items, Constraints):
            raise TypeError(f"Constraints(items=...) must be Constraints, got {self.items!r}")

    def _spec(self) -> dict[str, Any] | None:
        out: dict[str, Any] = {}
        for key in ("ge", "gt", "le", "lt"):
            v = getattr(self, key)
            if v is not None:
                out[key] = float(v)
        for key in ("min_length", "max_length", "pattern"):
            v = getattr(self, key)
            if v is not None:
                out[key] = v
        if self.one_of is not None:
            out["one_of"] = list(self.one_of)
        if self.items is not None and (inner := self.items._spec()):
            out["items"] = inner
        return out or None


@dataclass(frozen=True)
class Field:
    """One field of a `Struct`."""

    name: str
    type: TypeRef
    constraints: Constraints = field(default_factory=Constraints)

    def __post_init__(self) -> None:
        if not isinstance(self.name, str) or not self.name.isidentifier():
            raise ValueError(f"invalid field name {self.name!r}")
        _ref(self.type, f"field '{self.name}'")
        if not isinstance(self.constraints, Constraints):
            raise TypeError(f"field '{self.name}': constraints must be Constraints, got {self.constraints!r}")


@dataclass(frozen=True)
class Struct:
    """A named record type. Its name is how `T.struct(name)` refers to it, and must be
    unique in an Env: declaring two different structs with one name is an error."""

    name: str
    fields: tuple[Field, ...]

    def __init__(self, name: str, fields: Iterable[Field]) -> None:
        _check_struct_name(name)
        fs = tuple(fields)
        for f in fs:
            if not isinstance(f, Field):
                raise TypeError(f"struct '{name}': expected Field values, got {f!r}")
        seen: set[str] = set()
        for f in fs:
            if f.name in seen:
                raise ValueError(f"struct '{name}': field '{f.name}' is declared twice")
            seen.add(f.name)
        object.__setattr__(self, "name", name)
        object.__setattr__(self, "fields", fs)

    def _spec(self) -> list[tuple[str, TypeSpec, dict[str, Any] | None]]:
        return [(f.name, f.type._spec, f.constraints._spec()) for f in self.fields]
