"""Mapping Python types (builtins, Pydantic models, dataclasses) to CEL types."""

from __future__ import annotations

import dataclasses
import datetime as _dt
import decimal
import enum
import types
import typing
from collections.abc import Mapping, Sequence
from collections.abc import Set as AbstractSet
from typing import Any, Union, get_args, get_origin

TypeSpec = Any  # "int" | ("list", TypeSpec) | ("nullable", TypeSpec) | ("struct", name) | ...

_SCALARS: dict[Any, str] = {
    bool: "bool",
    int: "int",
    float: "double",
    str: "string",
    bytes: "bytes",
    _dt.date: "date",
    type(None): "null",
    Any: "dyn",
    object: "dyn",
}

_CEL_NAMES = {"bool", "int", "uint", "double", "string", "bytes", "null", "date", "dyn"}


def is_model(tp: Any) -> bool:
    return isinstance(tp, type) and hasattr(tp, "model_fields") and hasattr(tp, "model_validate")


def is_struct_class(tp: Any) -> bool:
    return is_model(tp) or (isinstance(tp, type) and dataclasses.is_dataclass(tp))


def type_name(spec: TypeSpec) -> str:
    if isinstance(spec, str):
        return spec
    kind = spec[0]
    if kind == "list":
        return f"list({type_name(spec[1])})"
    if kind == "map":
        return f"map({type_name(spec[1])}, {type_name(spec[2])})"
    if kind == "nullable":
        return f"{type_name(spec[1])}?"
    return spec[1]


class SchemaBuilder:
    """Collects struct declarations while converting Python annotations."""

    def __init__(self) -> None:
        self.structs: dict[str, list[tuple[str, TypeSpec, dict[str, Any] | None]]] = {}
        self.classes: dict[str, type] = {}

    def copy(self) -> SchemaBuilder:
        b = SchemaBuilder()
        b.structs = dict(self.structs)
        b.classes = dict(self.classes)
        return b

    # -- public -----------------------------------------------------------

    def convert(self, tp: Any, where: str) -> tuple[TypeSpec, dict[str, Any] | None]:
        """Return (type spec, constraints) for a Python annotation."""
        cons: dict[str, Any] = {}
        spec = self._convert(tp, cons, where)
        return spec, (cons or None)

    # -- internals --------------------------------------------------------

    def _struct_name(self, cls: type) -> str:
        name = cls.__name__
        existing = self.classes.get(name)
        if existing is not None and existing is not cls:
            name = f"{cls.__module__}.{cls.__qualname__}"
        return name

    def _register(self, cls: type) -> str:
        name = self._struct_name(cls)
        if name in self.structs:
            return name
        self.classes[name] = cls
        self.structs[name] = []  # placeholder for recursion
        fields: list[tuple[str, TypeSpec, dict[str, Any] | None]] = []
        if is_model(cls):
            for fname, info in cls.model_fields.items():  # type: ignore[attr-defined]
                cons: dict[str, Any] = {}
                _metadata_constraints(info.metadata, cons)
                spec = self._convert(info.annotation, cons, f"{name}.{fname}")
                fields.append((fname, spec, cons or None))
        else:
            hints = self._hints(cls, name)
            for f in dataclasses.fields(cls):
                cons = {}
                spec = self._convert(hints.get(f.name, Any), cons, f"{name}.{f.name}")
                fields.append((f.name, spec, cons or None))
        self.structs[name] = fields
        return name

    def _hints(self, cls: type, where: str) -> dict[str, Any]:
        # String annotations (``from __future__ import annotations``) on classes defined
        # inside a function cannot see that function's locals; give them the classes we know.
        known = {c.__name__: c for c in self.classes.values()}
        try:
            return typing.get_type_hints(cls, localns=known, include_extras=True)
        except NameError as exc:
            raise TypeError(
                f"{where}: cannot resolve annotation {exc.name!r}; define the class at module "
                f"level, or declare {exc.name} in the Env before {cls.__name__}"
            ) from None

    def _convert(self, tp: Any, cons: dict[str, Any], where: str) -> TypeSpec:
        if isinstance(tp, str) and tp in _CEL_NAMES:
            return tp
        if tp in _SCALARS:
            return _SCALARS[tp]
        if tp is decimal.Decimal:
            raise TypeError(
                f"{where}: Decimal has no exact CEL type; store money as integer minor units "
                "(e.g. cents: int) so the verifier can reason about it exactly"
            )
        if isinstance(tp, type) and issubclass(tp, enum.Enum):
            values = [m.value for m in tp]
            base = {type(v) for v in values}
            if base == {str}:
                cons["one_of"] = values
                return "string"
            if base == {int}:
                cons["one_of"] = values
                return "int"
            raise TypeError(f"{where}: enum {tp.__name__} must have all-str or all-int values")
        if is_struct_class(tp):
            return ("struct", self._register(typing.cast("type", tp)))
        origin = get_origin(tp)
        args = get_args(tp)
        if origin is typing.Annotated:
            _metadata_constraints(args[1:], cons)
            return self._convert(args[0], cons, where)
        if origin is typing.Literal:
            kinds = {type(a) for a in args}
            if kinds == {str}:
                cons["one_of"] = list(args)
                return "string"
            if kinds <= {int} and bool not in kinds:
                cons["one_of"] = list(args)
                return "int"
            if kinds == {bool}:
                return "bool"
            raise TypeError(f"{where}: Literal values must be all str or all int")
        if origin in (Union, types.UnionType):
            non_none = [a for a in args if a is not type(None)]
            if len(non_none) == 1 and len(non_none) < len(args):
                return ("nullable", self._convert(non_none[0], cons, where))
            raise TypeError(f"{where}: unions other than Optional[T] are not supported")
        if origin in (list, tuple, set, frozenset, Sequence, AbstractSet):
            if origin is tuple and len(args) == 2 and args[1] is Ellipsis:
                args = (args[0],)
            elif origin is tuple and len(set(args)) > 1:
                raise TypeError(f"{where}: heterogeneous tuples are not supported; use list[T]")
            item_cons: dict[str, Any] = {}
            elem = self._convert(args[0], item_cons, f"{where}[]") if args else "dyn"
            if item_cons:
                cons["items"] = item_cons
            return ("list", elem)
        if origin in (dict, Mapping):
            k = self._convert(args[0], {}, f"{where} key") if args else "dyn"
            v = self._convert(args[1], {}, f"{where} value") if args else "dyn"
            return ("map", k, v)
        if tp in (list, tuple, set, frozenset):
            return ("list", "dyn")
        if tp is dict:
            return ("map", "dyn", "dyn")
        raise TypeError(f"{where}: cannot map {tp!r} to a CEL type")


def _metadata_constraints(metadata: Sequence[Any], cons: dict[str, Any]) -> None:
    for m in metadata:
        for key in ("ge", "gt", "le", "lt", "min_length", "max_length", "pattern"):
            val = getattr(m, key, None)
            if val is not None and not callable(val):
                cons[key] = float(val) if key in ("ge", "gt", "le", "lt") else val
        # pydantic FieldInfo nested in Annotated[..., Field(...)]
        inner = getattr(m, "metadata", None)
        if isinstance(inner, list) and inner is not metadata:
            _metadata_constraints(inner, cons)


def from_cel(value: Any, spec: TypeSpec, schema: SchemaBuilder) -> Any:
    """Convert a raw CEL value (structs as dicts) back into Python classes."""
    if value is None or isinstance(spec, str):
        return value
    kind = spec[0]
    if kind == "nullable":
        return from_cel(value, spec[1], schema)
    if kind == "list":
        return [from_cel(v, spec[1], schema) for v in value]
    if kind == "map":
        return {k: from_cel(v, spec[2], schema) for k, v in value.items()}
    if kind == "struct":
        cls = schema.classes.get(spec[1])
        if cls is None:
            return value
        if is_model(cls):
            return cls.model_validate(dict(value))  # type: ignore[attr-defined]
        fields = {f: s for f, s, _ in schema.structs.get(spec[1], [])}
        return cls(**{k: from_cel(v, fields.get(k, "dyn"), schema) for k, v in value.items() if k in fields})
    return value


def cel_literal(value: Any) -> str:
    """Render a Python value as CEL source."""
    if value is None:
        return "null"
    if value is True:
        return "true"
    if value is False:
        return "false"
    if isinstance(value, enum.Enum):
        return cel_literal(value.value)
    if isinstance(value, int):
        return str(value) if value <= 2**63 - 1 else f"{value}u"
    if isinstance(value, float):
        r = repr(value)
        return r if any(c in r for c in ".eEn") else r + ".0"
    if isinstance(value, str):
        return '"' + value.replace("\\", "\\\\").replace('"', '\\"').replace("\n", "\\n") + '"'
    if isinstance(value, bytes):
        return "b" + cel_literal(value.decode("latin-1"))
    if isinstance(value, _dt.datetime):
        raise TypeError("datetime is not supported; use datetime.date")
    if isinstance(value, _dt.date):
        return f'date("{value.isoformat()}")'
    if isinstance(value, (list, tuple, set, frozenset)):
        items = sorted(value, key=repr) if isinstance(value, (set, frozenset)) else value
        return "[" + ", ".join(cel_literal(v) for v in items) + "]"
    if isinstance(value, Mapping):
        return "{" + ", ".join(f"{cel_literal(k)}: {cel_literal(v)}" for k, v in value.items()) + "}"
    raise TypeError(f"cannot render {type(value).__name__} as a CEL literal")
