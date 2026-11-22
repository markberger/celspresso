"""Mapping Python types (builtins, Pydantic models, dataclasses) to CEL types."""

from __future__ import annotations

import datetime as _dt
import decimal
import enum
import functools
import math
import sys
import types
import typing
from collections.abc import Callable, Iterable, Mapping, Sequence
from collections.abc import Set as AbstractSet
from typing import Any, Union, get_args, get_origin

from ._celspresso import pattern_error
from .schema import Constraints, Field, Struct, TypeRef, _check_struct_name

TypeSpec = Any  # "int" | ("list", TypeSpec) | ("nullable", TypeSpec) | ("struct", name) | ...

_SCALARS: dict[Any, str] = {
    bool: "bool",
    int: "int",
    float: "double",
    str: "string",
    bytes: "bytes",
    _dt.date: "date",
    _dt.datetime: "timestamp",
    _dt.timedelta: "duration",
    type(None): "null",
    Any: "dyn",
    object: "dyn",
}

_CEL_NAMES = {
    "bool",
    "int",
    "uint",
    "double",
    "string",
    "bytes",
    "null",
    "date",
    "timestamp",
    "duration",
    "dyn",
}


def is_model(tp: Any) -> bool:
    return isinstance(tp, type) and hasattr(tp, "model_fields") and hasattr(tp, "model_validate")


@functools.cache
def _default_adapters() -> tuple[Any, ...]:
    from .adapters import DataclassAdapter, PydanticAdapter

    return (PydanticAdapter(), DataclassAdapter())


class SchemaContext:
    """What a `TypeAdapter` gets while mapping a type: converting the types its fields
    are annotated with, and registering structs (with naming and recursion handled)."""

    __slots__ = ("_adapter", "_b", "_live")

    def __init__(self, builder: SchemaBuilder, adapter: Any) -> None:
        self._b = builder
        self._adapter = adapter
        self._live = True

    def _check_live(self) -> None:
        if not self._live:
            raise RuntimeError("a SchemaContext is only usable during the schema_for call it was passed to")

    def struct(self, key: Any, build: Callable[[], Iterable[Field]], *, name: str | None = None) -> TypeRef:
        """The struct for `key` (usually a class), calling `build()` for its fields the
        first time. `build` may convert types that refer back to `key`: recursion works.
        Keys are compared by equality if hashable (so a class, a string such as a
        protobuf full name, or a tuple), else by identity. If `build` raises, the struct
        (and any registered while building it) is forgotten.

        The struct is named `name` if given and free, else after the class
        (`Name`, then `module.Qualname`), with `#2`, `#3`, ... appended if taken."""
        self._check_live()
        if name is not None:
            _check_struct_name(name)
        return TypeRef._unchecked(("struct", self._b._register(key, self._adapter, build, name)))

    def convert(self, tp: Any, constraints: Constraints | None = None) -> tuple[TypeRef, Constraints]:
        """The CEL type for a Python annotation (through every adapter), and the
        constraints it carries, merged over `constraints`."""
        self._check_live()
        where = self._b._building[-1] if self._b._building else repr(tp)
        return self._convert(tp, constraints, where)

    def field(
        self,
        name: str,
        tp: Any,
        constraints: Constraints | None = None,
        *,
        reader: Callable[[Any], Any] | None = None,
    ) -> Field:
        """A struct field of Python type `tp`; for use inside `struct(..., build)`.
        `reader` reads the value from the containing object (see `schema.Field`)."""
        self._check_live()
        where = f"{self._b._building[-1]}.{name}" if self._b._building else name
        ref, cons = self._convert(tp, constraints, where)
        return Field(name, ref, cons, reader=reader)

    def type_hints(self, cls: type) -> dict[str, Any]:
        """`typing.get_type_hints(cls, include_extras=True)`, also resolving string
        annotations that name classes already registered (e.g. local classes)."""
        self._check_live()
        return self._b.type_hints(cls)

    def _convert(self, tp: Any, constraints: Constraints | None, where: str) -> tuple[TypeRef, Constraints]:
        cons: dict[str, Any] = dict(constraints._spec() or {}) if constraints is not None else {}
        if isinstance(tp, TypeRef):  # e.g. T.list(ref) of a ref this context returned
            self._b._check_refs(tp._spec, where, by_name=False)
            return tp, _constraints_of(cons)
        spec = self._b._convert(tp, cons, where)
        return TypeRef._unchecked(spec), _constraints_of(cons)


class _Id:
    """Identity key for an unhashable registration key."""

    __slots__ = ("n",)

    def __init__(self, obj: Any) -> None:
        self.n = id(obj)

    def __eq__(self, other: object) -> bool:
        return isinstance(other, _Id) and other.n == self.n

    def __hash__(self) -> int:
        return hash(self.n)


def _key_of(key: Any) -> Any:
    try:
        hash(key)
    except TypeError:
        return _Id(key)
    return key


def _constraints_of(d: dict[str, Any] | None) -> Constraints:
    if not d:
        return Constraints()
    return Constraints(
        **{k: v for k, v in d.items() if k not in ("one_of", "items")},
        one_of=tuple(d["one_of"]) if "one_of" in d else None,
        items=_constraints_of(d["items"]) if "items" in d else None,
    )


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

    def __init__(self, adapters: Iterable[Any] = ()) -> None:
        self.structs: dict[str, list[tuple[str, TypeSpec, dict[str, Any] | None]]] = {}
        # struct name -> {field name: reader}, for fields with a custom reader
        self.readers: dict[str, dict[str, Callable[[Any], Any]]] = {}
        # struct name -> (the key an adapter registered it under, that adapter)
        self.owners: dict[str, tuple[Any, Any]] = {}
        self._by_key: dict[Any, str] = {}  # _key_of(key) -> name; owners keeps the keys alive
        self._journal: list[str] = []  # names registered, in order, for rollback
        self.adapters: tuple[Any, ...] = _default_adapters()
        self._building: list[str] = []
        self.add_adapters(adapters)

    def copy(self) -> SchemaBuilder:
        b = SchemaBuilder.__new__(SchemaBuilder)
        b.structs = dict(self.structs)
        b.readers = dict(self.readers)
        b.owners = dict(self.owners)
        b._by_key = dict(self._by_key)
        b._journal = []
        b.adapters = self.adapters
        b._building = []
        return b

    def add_adapters(self, adapters: Iterable[Any]) -> None:
        """Put adapters ahead of the ones already here (they only affect types not yet seen)."""
        new = list(adapters)
        for a in new:
            if not (callable(getattr(a, "schema_for", None)) and callable(getattr(a, "decode", None))):
                raise TypeError(
                    f"adapters=[...] expects TypeAdapter objects (schema_for and decode), got {a!r}"
                )
        self.adapters = (*new, *self.adapters)

    @property
    def classes(self) -> dict[str, Any]:
        return {name: key for name, (key, _) in self.owners.items()}

    # -- public -----------------------------------------------------------

    def declare(self, structs: Iterable[Struct]) -> None:
        """Add `schema.Struct` declarations. Redeclaring a name is fine if the definition
        is identical; a different struct (or a class) under the same name is an error."""
        new = list(structs)
        for st in new:
            if not isinstance(st, Struct):
                raise TypeError(f"structs=[...] expects celspresso.schema.Struct values, got {st!r}")
            spec = st._spec()
            if st.name in self.structs:
                if st.name in self.owners:
                    raise ValueError(
                        f"struct name '{st.name}' is already used by {self.owners[st.name][0]!r}"
                    )
                if self.structs[st.name] != spec or self.readers.get(st.name, {}) != st._readers():
                    raise ValueError(f"struct '{st.name}' is already declared with different fields")
            self.structs[st.name] = spec
            self._set_readers(st.name, st._readers())
        for st in new:
            for f in st.fields:
                where = f"{st.name}.{f.name}"
                self._check_refs(f.type._spec, where, by_name=True)
                _check_constraints(f.type._spec, f.constraints, where)

    def _check_refs(self, spec: TypeSpec, where: str, *, by_name: bool) -> None:
        """Every struct `spec` mentions must exist. `by_name` refs (a user's T.struct) may
        not name an adapter's struct: those names depend on registration order."""
        if isinstance(spec, str):
            return
        if spec[0] == "struct":
            if by_name and spec[1] in self.owners:
                raise TypeError(
                    f"{where}: '{spec[1]}' is the struct for {self.owners[spec[1]][0]!r}; "
                    "use that type itself instead of T.struct"
                )
            if spec[1] not in self.structs:
                raise TypeError(f"{where}: unknown struct '{spec[1]}'; declare it with structs=[Struct(...)]")
            return
        for inner in spec[1:]:
            self._check_refs(inner, where, by_name=by_name)

    def convert(self, tp: Any, where: str) -> tuple[TypeSpec, dict[str, Any] | None]:
        """Return (type spec, constraints) for a Python annotation."""
        cons: dict[str, Any] = {}
        spec = self._convert(tp, cons, where)
        return spec, (cons or None)

    # -- adapter support ----------------------------------------------------

    def _struct_name(self, key: Any, preferred: str | None) -> str:
        """The first free one of `preferred` (else `Name`, `module.Qualname`), then
        `...#2`, `...#3`: distinct keys never share a name (Django migration models, for
        one, are distinct classes that all live in the same fake module)."""
        if preferred is not None:
            qualified, candidates = preferred, [preferred]
        else:
            qualname = getattr(key, "__qualname__", None)
            if not isinstance(qualname, str):
                raise TypeError(f"cannot name a struct for {key!r}; pass name= to ctx.struct")
            qualified = f"{key.__module__}.{qualname}"
            candidates = [key.__name__, qualified]
        n = 2
        while True:
            for name in candidates:
                if name not in self.structs:  # taken by an adapter or a declared Struct
                    return name
            candidates = [f"{qualified}#{n}"]
            n += 1

    def _register(
        self, key: Any, adapter: Any, build: Callable[[], Iterable[Field]], preferred: str | None
    ) -> str:
        known = self._by_key.get(_key_of(key))
        if known is not None:
            return known
        name = self._struct_name(key, preferred)
        mark = len(self._journal)
        self.owners[name] = (key, adapter)
        self._by_key[_key_of(key)] = name
        self.structs[name] = []  # placeholder: fields may refer back to this struct
        self._journal.append(name)
        self._building.append(name)
        try:
            return self._finish(name, build)
        except BaseException:
            # undo this struct and everything registered while building it (which may
            # refer to it), so an adapter that catches the error sees no half-built struct
            for undone in self._journal[mark:]:
                k, _ = self.owners.pop(undone)
                del self._by_key[_key_of(k)]
                del self.structs[undone]
                self.readers.pop(undone, None)
            del self._journal[mark:]
            raise
        finally:
            self._building.pop()

    def _finish(self, name: str, build: Callable[[], Iterable[Field]]) -> str:
        fields = list(build())
        seen: set[str] = set()
        out: list[tuple[str, TypeSpec, dict[str, Any] | None]] = []
        for f in fields:
            if not isinstance(f, Field):
                raise TypeError(f"{name}: an adapter's struct fields must be schema.Field values, got {f!r}")
            if f.name in seen:
                raise ValueError(f"{name}: field '{f.name}' is declared twice")
            seen.add(f.name)
            where = f"{name}.{f.name}"
            self._check_refs(f.type._spec, where, by_name=False)
            _check_constraints(f.type._spec, f.constraints, where)
            out.append((f.name, f.type._spec, f.constraints._spec()))
        self.structs[name] = out
        self._set_readers(name, {f.name: f.reader for f in fields if f.reader is not None})
        return name

    def _set_readers(self, name: str, readers: dict[str, Callable[[Any], Any]]) -> None:
        if readers:
            self.readers[name] = readers
        else:
            self.readers.pop(name, None)

    def type_hints(self, cls: type) -> dict[str, Any]:
        where = self._by_key.get(_key_of(cls), cls.__name__)
        # String annotations (``from __future__ import annotations``) on classes defined
        # inside a function cannot see that function's locals; give them the classes we know.
        # Names the class's own module defines win: `localns` outranks module globals
        # in get_type_hints, so a same-named class from elsewhere would hide them.
        module = sys.modules.get(cls.__module__)
        own = vars(module) if module is not None else {}
        known = {
            k.__name__: k for k, _ in self.owners.values() if isinstance(k, type) and k.__name__ not in own
        }
        try:
            return typing.get_type_hints(cls, localns=known, include_extras=True)
        except NameError as exc:
            raise TypeError(
                f"{where}: cannot resolve annotation {exc.name!r}; define the class at module "
                f"level, or declare {exc.name} in the Env before {cls.__name__}"
            ) from None

    def _convert(self, tp: Any, cons: dict[str, Any], where: str) -> TypeSpec:
        if isinstance(tp, TypeRef):
            self._check_refs(tp._spec, where, by_name=True)
            return tp._spec
        for adapter in self.adapters:
            ctx = SchemaContext(self, adapter)
            try:
                result = adapter.schema_for(tp, ctx)
            finally:
                ctx._live = False
            if result is None:
                continue
            ref, extra = result if isinstance(result, tuple) else (result, None)
            if not isinstance(ref, TypeRef) or not (extra is None or isinstance(extra, Constraints)):
                raise TypeError(
                    f"{where}: {type(adapter).__name__}.schema_for must return a TypeRef, "
                    f"(TypeRef, Constraints) or None, got {result!r}"
                )
            self._check_refs(ref._spec, where, by_name=False)
            for k, v in (extra._spec() or {} if extra is not None else {}).items():
                cons.setdefault(k, v)  # the annotation's own constraints win
            return ref._spec
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


_NUMERIC = {"int", "uint", "double"}
_SIZED = {"string", "bytes", "list", "map"}


def _check_constraints(spec: TypeSpec, c: Constraints, where: str) -> None:
    """Reject constraints that don't apply to the field's type, so the verifier (which
    would ignore them) and `evaluate` (which might reject every value) can't disagree."""
    if isinstance(spec, tuple) and spec[0] == "nullable":
        spec = spec[1]
    kind = spec if isinstance(spec, str) else spec[0]

    def bad(what: str, applies_to: str) -> TypeError:
        return TypeError(f"{where}: {what} applies to {applies_to}, not {type_name(spec)}")

    bounds = {k: v for k in ("ge", "gt", "le", "lt") if (v := getattr(c, k)) is not None}
    if bounds and kind not in _NUMERIC:
        raise bad("a numeric bound", "int, uint or double")
    if kind == "uint" and (bounds.get("le", 0) < 0 or bounds.get("lt", 1) <= 0):
        raise ValueError(f"{where}: no uint satisfies {bounds}")
    # (bound, strict): on a tie between ge and gt, the strict one is the binding bound
    lo = max((bounds.get("ge", -math.inf), False), (bounds.get("gt", -math.inf), True))
    hi = min(
        (bounds.get("le", math.inf), False),
        (bounds.get("lt", math.inf), True),
        key=lambda b: (b[0], not b[1]),
    )
    if lo[0] > hi[0] or (lo[0] == hi[0] and (lo[1] or hi[1])):
        raise ValueError(f"{where}: no value satisfies {bounds}")
    if (c.min_length is not None or c.max_length is not None) and kind not in _SIZED:
        raise bad("a length", "string, bytes, list or map")
    if c.min_length is not None and c.max_length is not None and c.min_length > c.max_length:
        raise ValueError(f"{where}: min_length {c.min_length} exceeds max_length {c.max_length}")
    if c.pattern is not None:
        if kind != "string":
            raise bad("a pattern", "string")
        if (err := pattern_error(c.pattern)) is not None:
            raise ValueError(f"{where}: {err}")
    if c.one_of is not None:
        if isinstance(c.one_of[0], str):
            if kind != "string":
                raise bad("one_of with strings", "string")
        elif kind == "int":
            if not all(-(2**63) <= v < 2**63 for v in c.one_of):
                raise ValueError(f"{where}: one_of values must fit in int64")
        elif kind == "uint":
            if not all(v >= 0 for v in c.one_of):
                raise ValueError(f"{where}: one_of values must be non-negative for uint")
        else:
            raise bad("one_of with ints", "int or uint")
    if c.items is not None:
        if kind != "list":
            raise bad("items", "list")
        _check_constraints(spec[1], c.items, f"{where}[]")


def _metadata_constraints(metadata: Sequence[Any], cons: dict[str, Any]) -> None:
    for m in metadata:
        for key in ("ge", "gt", "le", "lt", "min_length", "max_length", "pattern"):
            val = getattr(m, key, None)
            if val is not None and not callable(val):
                if key in ("ge", "gt", "le", "lt"):
                    val = float(val)
                elif key == "pattern" and not isinstance(val, str):
                    val = getattr(val, "pattern", val)  # a compiled re.Pattern
                cons[key] = val
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
        fields = {f: s for f, s, _ in schema.structs.get(spec[1], [])}
        data = {k: from_cel(v, fields.get(k, "dyn"), schema) for k, v in value.items()}
        owner = schema.owners.get(spec[1])
        if owner is None:  # a declared Struct: stays a dict
            return data
        key, adapter = owner
        return adapter.decode(key, data)
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
        if value.utcoffset() is None:
            raise TypeError("naive datetime has no time zone; attach one, e.g. tzinfo=datetime.timezone.utc")
        utc = value.astimezone(_dt.timezone.utc).replace(tzinfo=None)
        return f'timestamp("{utc.isoformat()}Z")'
    if isinstance(value, _dt.timedelta):
        micros = (value.days * 86_400 + value.seconds) * 1_000_000 + value.microseconds
        sign, micros = ("-", -micros) if micros < 0 else ("", micros)
        return f'duration("{sign}{micros // 1_000_000}s{micros % 1_000_000}us")'
    if isinstance(value, _dt.date):
        return f'date("{value.isoformat()}")'
    if isinstance(value, (list, tuple, set, frozenset)):
        items = sorted(value, key=repr) if isinstance(value, (set, frozenset)) else value
        return "[" + ", ".join(cel_literal(v) for v in items) + "]"
    if isinstance(value, Mapping):
        return "{" + ", ".join(f"{cel_literal(k)}: {cel_literal(v)}" for k, v in value.items()) + "}"
    raise TypeError(f"cannot render {type(value).__name__} as a CEL literal")
