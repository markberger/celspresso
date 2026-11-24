"""celspresso.adapters: teaching celspresso foreign type systems."""

from __future__ import annotations

import dataclasses
import pickle
from typing import Annotated, Any, ClassVar, NewType

import annotated_types
import pydantic
import pytest

from celspresso import Env
from celspresso.adapters import (
    DataclassAdapter,
    PydanticAdapter,
    SchemaContext,
    TypeAdapter,
    constraints_from,
)
from celspresso.schema import Constraints, Field, Struct, T, TypeRef


class Table:
    """A tiny stand-in for an ORM model: columns described by a class attribute."""

    columns: ClassVar[dict[str, Any]] = {}
    label: ClassVar[str | None] = None


class Customer(Table):
    label = "crm.Customer"
    columns: ClassVar[dict[str, Any]] = {"name": str, "credit": Annotated[int, annotated_types.Ge(0)]}


class Account(Table):
    label = "crm.Account"
    columns: ClassVar[dict[str, Any]] = {"owner": Customer, "parent": "Account | None", "balance": int}


@dataclasses.dataclass
class Record:
    """What `TableAdapter.decode` builds."""

    table: type
    values: dict[str, Any]


class TableAdapter:
    def __init__(self) -> None:
        self.decoded: list[type] = []

    def schema_for(self, tp: Any, ctx: SchemaContext) -> TypeRef | None:
        if not (isinstance(tp, type) and issubclass(tp, Table)):
            return None

        def build() -> list[Field]:
            return [
                ctx.field(n, Account | None if t == "Account | None" else t) for n, t in tp.columns.items()
            ]

        return ctx.struct(tp, build, name=tp.label)

    def decode(self, tp: Any, data: dict[str, Any]) -> Any:
        self.decoded.append(tp)
        return Record(tp, data)


def test_builtin_adapters_satisfy_the_protocol() -> None:
    assert isinstance(PydanticAdapter(), TypeAdapter)
    assert isinstance(DataclassAdapter(), TypeAdapter)
    assert isinstance(TableAdapter(), TypeAdapter)


def test_a_custom_adapter_maps_structs_with_recursion_and_nesting() -> None:
    adapter = TableAdapter()
    env = Env(acct=Account, adapters=[adapter])
    assert env.variables == {"acct": "crm.Account"}
    assert "crm.Customer\n    name: string\n    credit: int, >= 0" in env.describe()
    assert "parent: crm.Account or null" in env.describe()
    # constraints from the adapter's fields are facts for the prover
    assert env.predicate("acct.owner.credit < 0").satisfiable().refuted
    p = env.predicate("acct.parent == null || acct.parent.balance >= acct.balance")
    v = p.always_true()
    assert v.refuted
    assert v.counterexample is not None
    rec = v.counterexample.to_python()["acct"]
    assert isinstance(rec, Record)
    assert rec.table is Account
    assert isinstance(rec.values["owner"], Record)  # nested values decoded first
    assert isinstance(rec.values["parent"], Record)
    assert rec.values["parent"].values["balance"] < rec.values["balance"]
    # values are read from mappings or attributes named like the fields
    row = {"owner": {"name": "a", "credit": 1}, "parent": None, "balance": 3}
    assert p.evaluate({"acct": row})


@dataclasses.dataclass
class Invoice:
    account: Account
    amount: int


@dataclasses.dataclass
class Batch:
    invoices: Annotated[list[Invoice], annotated_types.MaxLen(3)]


def test_adapters_compose_with_the_builtin_ones() -> None:
    env = Env(batch=Batch, adapters=[TableAdapter()])
    v = env.predicate("batch.invoices.all(i, i.amount <= i.account.balance)").always_true()
    assert v.refuted
    assert v.counterexample is not None
    batch = v.counterexample.to_python()["batch"]
    assert isinstance(batch, Batch)
    assert isinstance(batch.invoices[0], Invoice)
    assert isinstance(batch.invoices[0].account, Record)


def test_user_adapters_come_before_the_builtin_ones() -> None:
    @dataclasses.dataclass
    class Secret:
        public: int
        password: str

    class HidePasswords:
        def schema_for(self, tp: Any, ctx: SchemaContext) -> TypeRef | None:
            if tp is not Secret:
                return None
            return ctx.struct(tp, lambda: [ctx.field("public", int)])

        def decode(self, tp: Any, data: dict[str, Any]) -> Any:
            return tp(password="", **data)

    env = Env(s=Secret, adapters=[HidePasswords()])
    assert "password" not in env.describe()
    w = env.predicate("s.public == 4").satisfiable().witness
    assert w is not None
    assert w.to_python()["s"] == Secret(4, "")
    assert Env(s=Secret).predicate("s.password == 'x'").satisfiable().proved


Cents = NewType("Cents", int)


class CentsAdapter:
    """A type-level mapping: no struct, just a CEL type and the constraints it implies."""

    def schema_for(self, tp: Any, ctx: SchemaContext) -> tuple[TypeRef, Constraints] | None:
        return (T.int, Constraints(ge=0, le=10**12)) if tp is Cents else None

    def decode(self, tp: Any, data: dict[str, Any]) -> Any:  # pragma: no cover - not a struct
        raise AssertionError


def test_scalar_mappings_with_implied_constraints() -> None:
    @dataclasses.dataclass
    class Line:
        price: Cents
        refund: Annotated[Cents, annotated_types.Le(500)]
        prices: Annotated[list[Cents], annotated_types.MaxLen(3)]

    env = Env(line=Line, total=Cents, adapters=[CentsAdapter()])
    assert env.variables == {"line": "Line", "total": "int"}
    assert "price: int, >= 0, <= 1000000000000" in env.describe()
    assert "refund: int, >= 0, <= 500" in env.describe()  # the annotation's own bound wins
    assert env.predicate("line.price < 0 || line.refund > 500").satisfiable().refuted
    assert env.predicate("total < 0").satisfiable().refuted  # variables carry them too
    assert env.predicate("line.prices.exists(p, p < 0)").satisfiable().refuted
    with pytest.raises(ValueError, match="violates the schema"):
        env.predicate("true").evaluate({"line": {"price": -1, "refund": 0, "prices": []}, "total": 0})


def test_struct_naming() -> None:
    class Thing:
        pass

    class Named:
        def __init__(self, names: dict[Any, str | None]) -> None:
            self.names = names

        def schema_for(self, tp: Any, ctx: SchemaContext) -> TypeRef | None:
            if tp not in self.names:
                return None
            return ctx.struct(tp, lambda: [ctx.field("v", int)], name=self.names[tp])

        def decode(self, tp: Any, data: dict[str, Any]) -> Any:
            return data

    key_a, key_b = object(), object()
    taken = Struct("shop.Order", [Field("x", T.string)])
    env = Env(
        structs=[taken],
        a=key_a,
        b=key_b,
        thing=Thing,
        adapters=[Named({key_a: "shop.Order", key_b: "shop.Order", Thing: None})],
    )
    # a taken preferred name gets a suffix; an unnamed class is named after itself
    assert env.variables == {"a": "shop.Order#2", "b": "shop.Order#3", "thing": "Thing"}
    with pytest.raises(TypeError, match=r"pass name= to ctx\.struct"):
        Env(x=key_a, adapters=[Named({key_a: None})])
    with pytest.raises(ValueError, match="invalid struct name"):
        Env(x=key_a, adapters=[Named({key_a: "not valid"})])


def test_adapter_mistakes_are_reported() -> None:
    class Bad:
        def __init__(self, result: Any) -> None:
            self.result = result

        def schema_for(self, tp: Any, ctx: SchemaContext) -> Any:
            if tp is not Table:
                return None
            r = self.result
            return ctx.struct(tp, lambda: r) if isinstance(r, list) else r

        def decode(self, tp: Any, data: dict[str, Any]) -> Any:  # pragma: no cover
            return data

    with pytest.raises(TypeError, match=r"Bad.schema_for must return a TypeRef"):
        Env(t=Table, adapters=[Bad("int")])
    with pytest.raises(TypeError, match=r"Bad.schema_for must return a TypeRef"):
        Env(t=Table, adapters=[Bad((T.int, {"ge": 1}))])
    with pytest.raises(TypeError, match=r"must be schema\.Field values"):
        Env(t=Table, adapters=[Bad([("v", T.int)])])
    with pytest.raises(ValueError, match="field 'v' is declared twice"):
        Env(t=Table, adapters=[Bad([Field("v", T.int), Field("v", T.int)])])
    with pytest.raises(TypeError, match="unknown struct 'Nope'"):
        Env(t=Table, adapters=[Bad([Field("v", T.struct("Nope"))])])
    with pytest.raises(TypeError, match=r"Table.v: a pattern applies to string"):
        Env(t=Table, adapters=[Bad([Field("v", T.int, Constraints(pattern="x"))])])
    with pytest.raises(TypeError, match="expects TypeAdapter objects"):
        Env(adapters=[object()])
    with pytest.raises(TypeError, match="'adapters' is an Env option"):
        Env(adapters=TableAdapter)  # type: ignore[arg-type]
    assert Env({"adapters": int}).variables == {"adapters": "int"}


def test_extend_with_adapters() -> None:
    env = Env(n=int).extend(acct=Account, adapters=[TableAdapter()])
    assert env.variables == {"n": "int", "acct": "crm.Account"}
    assert env.extend(c=Customer).variables["c"] == "crm.Customer"  # adapters are kept
    with pytest.raises(TypeError, match="cannot map"):
        Env(n=int).extend(acct=Account)


def test_envs_with_different_adapters_for_one_type_are_different() -> None:
    class Other(TableAdapter):
        pass

    a = Env(c=Customer, adapters=[TableAdapter()])
    b = Env(c=Customer, adapters=[Other()])
    assert a.variables == b.variables
    with pytest.raises(ValueError, match="different environments"):
        a.predicate("c.credit > 0") & b.predicate("c.credit > 1")


def test_context_helpers() -> None:
    seen: dict[str, Any] = {}

    class Probe:
        def schema_for(self, tp: Any, ctx: SchemaContext) -> TypeRef | None:
            if tp is not Table:
                return None
            seen["outside"] = ctx.convert(Annotated[list[int], annotated_types.MaxLen(3)])

            def build() -> list[Field]:
                seen["inside"] = ctx.convert(int, Constraints(ge=1))
                return [ctx.field("v", Annotated[int, annotated_types.Lt(9)], Constraints(ge=1))]

            return ctx.struct(tp, build)

        def decode(self, tp: Any, data: dict[str, Any]) -> Any:  # pragma: no cover
            return data

    env = Env(t=Table, adapters=[Probe()])
    assert seen["outside"] == (T.list(T.int), Constraints(max_length=3))
    assert seen["inside"] == (T.int, Constraints(ge=1))
    assert "v: int, >= 1, < 9" in env.describe()


def test_constraints_from_metadata() -> None:
    assert constraints_from([annotated_types.Ge(1), annotated_types.MaxLen(4)]) == Constraints(
        ge=1, max_length=4
    )
    info = pydantic.Field(gt=0, pattern=r"^\d+$")
    assert constraints_from([info]) == Constraints(gt=0, pattern=r"^\d+$")
    assert constraints_from([]) == Constraints()
    assert constraints_from(["unrelated", 3]) == Constraints()


def test_compiled_patterns_in_metadata() -> None:
    import re

    class M(pydantic.BaseModel):
        code: Annotated[str, pydantic.StringConstraints(pattern=re.compile(r"^[A-Z]{3}$"))]

    assert Env(m=M).predicate("m.code == 'abc'").satisfiable().refuted


def test_local_class_names_survive_pickling() -> None:
    @dataclasses.dataclass
    class Local:
        v: int

    env = Env(x=Local)
    ref = TypeRef._unchecked(("struct", env.variables["x"]))
    assert pickle.loads(pickle.dumps(ref)) == ref


def test_context_refs_can_be_wrapped_and_passed_back() -> None:
    # e.g. a Django reverse relation: a list of another model's struct, where the
    # models are historical versions sharing a preferred name (so it gets a #n suffix)
    @dataclasses.dataclass
    class Line:
        qty: int

    class Model:
        def __init__(self, name: str, lines: type) -> None:
            self.name, self.lines = name, lines

    old, new = Model("app.Order@0003", Line), Model("app.Order@0003", Line)

    class Versions:
        def schema_for(self, tp: Any, ctx: SchemaContext) -> TypeRef | None:
            if not isinstance(tp, Model):
                return None
            line = ctx.convert(tp.lines)[0]
            return ctx.struct(
                tp,
                lambda: [
                    ctx.field("lines", T.list(line), Constraints(max_length=8)),
                    ctx.field("first", T.nullable(line)),
                ],
                name=tp.name,
            )

        def decode(self, tp: Any, data: dict[str, Any]) -> Any:
            return data

    env = Env(a=old, b=new, adapters=[Versions()])
    assert env.variables == {"a": "app.Order@0003", "b": "app.Order@0003#2"}
    assert env.predicate("a.lines.all(l, l.qty > 0) && b.first.qty < 0").satisfiable().proved


def test_equal_keys_share_one_struct() -> None:
    # a protobuf-style adapter keyed by full name, building a fresh string each time
    messages = {"pkg.Node": {"value": int, "next": "pkg.Node"}}

    class Message:
        def __init__(self, full_name: str) -> None:
            self.full_name = full_name

    class Proto:
        def schema_for(self, tp: Any, ctx: SchemaContext) -> TypeRef | None:
            if not isinstance(tp, Message):
                return None
            key = "".join(tp.full_name)  # equal, not identical, every call

            def build() -> list[Field]:
                return [
                    ctx.field(n, T.nullable(ctx.convert(Message(t))[0]) if isinstance(t, str) else t)
                    for n, t in messages[key].items()
                ]

            return ctx.struct(key, build, name=key)

        def decode(self, tp: Any, data: dict[str, Any]) -> Any:
            return data

    env = Env(n=Message("pkg.Node"), adapters=[Proto()])
    assert env.variables == {"n": "pkg.Node"}
    assert env.predicate("n.next.next.value == 3").satisfiable().proved


def test_a_failed_build_leaves_nothing_behind() -> None:
    import uuid

    class Author: ...

    class Book: ...

    class Shelf: ...

    tables: dict[type, dict[str, Any]] = {
        Author: {"id": uuid.UUID, "name": str},  # uuid.UUID is unmappable
        Book: {"author": Author, "title": str},
        Shelf: {"book": Book, "favourite": Author},
    }

    class Lenient:
        """Falls back to a string for fields it can't map."""

        def schema_for(self, tp: Any, ctx: SchemaContext) -> TypeRef | None:
            if tp not in tables:
                return None

            def field(n: str, t: Any) -> Field:
                try:
                    return ctx.field(n, t)
                except TypeError:
                    if tp is Author:
                        raise  # Author's own build fails...
                    return Field(n, T.string)  # ...and Book/Shelf fall back

            def build() -> list[Field]:
                return [field(n, t) for n, t in tables[tp].items()]

            return ctx.struct(tp, build)

        def decode(self, tp: Any, data: dict[str, Any]) -> Any:
            return data

    env = Env(s=Shelf, adapters=[Lenient()])
    # Author failed to build inside Book; it must not linger as an empty struct
    assert "Author" not in env.describe()
    assert env.predicate("s.book.author == 'x' && s.favourite == 'y'").satisfiable().proved


def test_a_stored_context_is_dead_after_schema_for() -> None:
    kept: list[SchemaContext] = []

    class Keeper:
        def schema_for(self, tp: Any, ctx: SchemaContext) -> TypeRef | None:
            kept.append(ctx)
            return None

        def decode(self, tp: Any, data: dict[str, Any]) -> Any:  # pragma: no cover
            return data

    Env(x=int, adapters=[Keeper()])
    for call in (
        lambda c: c.struct(Table, list),
        lambda c: c.convert(int),
        lambda c: c.field("x", int),
        lambda c: c.type_hints(Table),
    ):
        with pytest.raises(RuntimeError, match="only usable during the schema_for call"):
            call(kept[0])


def test_decode_errors_other_than_valueerror_propagate() -> None:
    @dataclasses.dataclass
    class Checked:
        v: int

        def __post_init__(self) -> None:
            if self.v == 7:
                raise RuntimeError("seven is unlucky")

    v = Env(c=Checked).predicate("c.v == 7").satisfiable()
    assert v.unknown  # a dataclass validator's rejection still means UNKNOWN
    assert v.reason is not None
    assert "fails model validation" in v.reason

    class Buggy(TableAdapter):
        def decode(self, tp: Any, data: dict[str, Any]) -> Any:
            raise AttributeError("adapter bug")

    with pytest.raises(AttributeError, match="adapter bug"):
        Env(c=Customer, adapters=[Buggy()]).predicate("c.credit == 1").satisfiable()
