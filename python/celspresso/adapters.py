"""Teach celspresso a type system: map foreign types (ORM models, protobuf messages, ...)
to CEL types.

celspresso's own support for Pydantic models and dataclasses is built from these same
pieces (`PydanticAdapter`, `DataclassAdapter`). An adapter answers two questions:

- `schema_for(tp, ctx)`: is `tp` mine, and if so what CEL type is it? Usually that is
  a struct, registered with `ctx.struct(tp, build)`, where `build` lists its fields;
  `ctx.field(name, annotation)` converts each field's annotation through every
  adapter, so a Django model's field may be a Pydantic model and vice versa.
- `decode(tp, data)`: rebuild a `tp` from a verifier witness, given its fields as a
  dict (already decoded). Return the dict itself if there is nothing better to build.
  Raise `ValueError` if the data can't be a real `tp` (a validator rejects it): the
  verdict becomes UNKNOWN. Any other exception is treated as a bug and propagates.
  The dict is keyed by field name, even for a field with a `reader` that reads some
  other attribute.

A `SchemaContext` is only valid during the `schema_for` call it was passed to.

>>> import dataclasses
>>> from celspresso import Env
>>> from celspresso.adapters import SchemaContext
>>> class Row:  # a class celspresso knows nothing about
...     columns = {"id": int, "email": str}
>>> class RowAdapter:
...     def schema_for(self, tp, ctx: SchemaContext):
...         if not (isinstance(tp, type) and issubclass(tp, Row)):
...             return None
...         return ctx.struct(tp, lambda: [ctx.field(n, t) for n, t in tp.columns.items()])
...
...     def decode(self, tp, data):
...         return data
>>> env = Env(row=Row, adapters=[RowAdapter()])
>>> env.variables
{'row': 'Row'}
>>> env.predicate("row.id > 0 && row.email.endsWith('@example.com')").satisfiable().sat
True

Values are read from attributes or mapping keys named like the fields, unless a field
has a `reader`: `ctx.field("lines", list[Line], reader=lambda o: o.line_set.all())`
reads a relation that isn't itself a list. See `schema.Field`.
"""

from __future__ import annotations

import dataclasses
import typing
from typing import TYPE_CHECKING, Any, Protocol, runtime_checkable

from ._types import SchemaContext, _constraints_of, _metadata_constraints, is_model

if TYPE_CHECKING:
    from collections.abc import Iterable

    from .schema import Constraints, TypeRef

__all__ = ["DataclassAdapter", "PydanticAdapter", "SchemaContext", "TypeAdapter", "constraints_from"]


@runtime_checkable
class TypeAdapter(Protocol):
    """Maps the types of one foreign type system to CEL types. See the module docs."""

    def schema_for(self, tp: Any, ctx: SchemaContext) -> TypeRef | tuple[TypeRef, Constraints] | None:
        """The CEL type of `tp` (optionally with constraints its values always satisfy),
        or None if `tp` isn't this adapter's."""
        ...

    def decode(self, tp: Any, data: dict[str, Any]) -> Any:
        """A `tp` value built from a struct's decoded fields; `ValueError` if invalid."""
        ...


def constraints_from(metadata: Iterable[Any]) -> Constraints:
    """Constraints from annotation metadata: `annotated_types` (`Ge(0)`, `MaxLen(5)`, ...),
    Pydantic `Field(...)` info, or anything else with `ge`/`gt`/`le`/`lt`/`min_length`/
    `max_length`/`pattern` attributes. Use it for `Annotated[...]` extras of your own."""
    cons: dict[str, Any] = {}
    _metadata_constraints(list(metadata), cons)
    return _constraints_of(cons)


class PydanticAdapter:
    """Pydantic models, as structs of their fields; witnesses via `model_validate`."""

    def schema_for(self, tp: Any, ctx: SchemaContext) -> TypeRef | None:
        if not is_model(tp):
            return None

        def build() -> list[Any]:
            return [
                # the metadata goes in as Annotated, so a Decimal's max_digits and
                # decimal_places reach its conversion (constraints_from would drop them)
                ctx.field(
                    name,
                    typing.Annotated[(info.annotation, *info.metadata)] if info.metadata else info.annotation,
                )
                for name, info in tp.model_fields.items()
            ]

        return ctx.struct(tp, build)

    def decode(self, tp: Any, data: dict[str, Any]) -> Any:
        return tp.model_validate(data)


class DataclassAdapter:
    """Dataclasses, as structs of their fields."""

    def schema_for(self, tp: Any, ctx: SchemaContext) -> TypeRef | None:
        if not (isinstance(tp, type) and dataclasses.is_dataclass(tp)):
            return None

        def build() -> list[Any]:
            hints = ctx.type_hints(tp)
            return [ctx.field(f.name, hints.get(f.name, Any)) for f in dataclasses.fields(tp)]

        return ctx.struct(tp, build)

    def decode(self, tp: Any, data: dict[str, Any]) -> Any:
        init = {f.name for f in dataclasses.fields(tp) if f.init}
        try:
            return tp(**{k: v for k, v in data.items() if k in init})
        except Exception as exc:  # __post_init__ validators may raise anything
            raise ValueError(f"{tp.__name__} rejected the witness: {exc!r}") from exc
