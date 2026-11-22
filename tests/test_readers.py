"""Custom field readers: values that aren't a plain attribute or mapping key."""

from __future__ import annotations

from typing import TYPE_CHECKING, Any

import pytest

from celspresso import Env, _celspresso
from celspresso.schema import Constraints, Field, Struct, T

if TYPE_CHECKING:
    from celspresso.adapters import SchemaContext
    from celspresso.schema import TypeRef


class Manager:
    """Like a Django related manager: not iterable, `.all()` gives the rows."""

    def __init__(self, rows: list[Any]) -> None:
        self._rows = rows

    def all(self) -> list[Any]:
        return list(self._rows)


class Line:
    def __init__(self, cents: int) -> None:
        self.cents = cents


class Order:
    def __init__(self, lines: list[Line], note: str | None = None) -> None:
        self.line_set = Manager(lines)  # the reverse relation, under its own name
        self.note = note


class OrderAdapter:
    """Maps Order/Line the way an ORM adapter would, reading `lines` through the manager."""

    def schema_for(self, tp: Any, ctx: SchemaContext) -> TypeRef | None:
        if tp is Line:
            return ctx.struct(Line, lambda: [ctx.field("cents", int, Constraints(ge=0))])
        if tp is Order:
            return ctx.struct(
                Order,
                lambda: [
                    ctx.field(
                        "lines",
                        list[Line],
                        Constraints(max_length=6),
                        reader=lambda o: o.line_set.all(),
                    ),
                    ctx.field("note", str | None),
                ],
            )
        return None

    def decode(self, tp: Any, data: dict[str, Any]) -> Any:
        return data


def test_an_adapter_reads_a_relation_through_its_manager() -> None:
    env = Env(order=Order, adapters=[OrderAdapter()])
    total = env.expr("order.lines.map(l, l.cents).sum()", int)
    assert total.evaluate({"order": Order([Line(250), Line(1000)])}) == 1250
    assert env.predicate("order.note == null").evaluate({"order": Order([])})
    # proofs see only the type and constraints: readers change nothing there
    assert total.bounds().max is not None
    assert env.predicate("order.lines.size() <= 6").always_true().proved


def test_reader_results_are_converted_and_validated() -> None:
    env = Env(order=Order, adapters=[OrderAdapter()])
    size = env.expr("order.lines.size()", int)
    with pytest.raises(TypeError, match=r"expected int at 'order\.lines\[0\]\.cents', got str"):
        size.evaluate({"order": Order([Line("x")])})  # type: ignore[arg-type]
    with pytest.raises(ValueError, match=r"order\.lines"):  # max_length=6 is enforced
        size.evaluate({"order": Order([Line(1)] * 7)})
    with pytest.raises(ValueError, match="cents"):  # ge=0 on the nested struct too
        size.evaluate({"order": Order([Line(-1)])})


def test_reader_exceptions_propagate() -> None:
    class Boom(Exception):
        pass

    def explode(_: Any) -> Any:
        raise Boom("db is down")

    item = Struct("Item", [Field("qty", T.int, reader=explode)])
    env = Env(structs=[item], item=T.struct("Item"))
    with pytest.raises(Boom):
        env.predicate("item.qty > 0").evaluate({"item": {}})


def test_declared_structs_take_readers() -> None:
    # e.g. a column stored under another key, or a computed value
    item = Struct(
        "Item",
        [
            Field("qty", T.int, reader=lambda row: row["QTY"]),
            Field("code", T.nullable(T.string), reader=lambda row: row.get("sku")),
        ],
    )
    env = Env(structs=[item], items=T.list(T.struct("Item")))
    pred = env.predicate("items.all(i, i.qty > 0) && items.exists(i, i.code == 'A1')")
    assert pred.evaluate({"items": [{"QTY": 2, "sku": "A1"}, {"QTY": 1}]})
    # explain and RuleSet go through the same conversion
    assert "→  True" in str(pred.explain({"items": [{"QTY": 2, "sku": "A1"}]}))
    # readers survive extend
    assert env.extend(n=int).predicate("items.size() == n").evaluate({"items": [{"QTY": 1}], "n": 1})


def test_reader_mistakes() -> None:
    with pytest.raises(TypeError, match="reader must be callable"):
        Field("qty", T.int, reader="QTY")  # type: ignore[arg-type]

    # redeclaring a struct is fine only if it's identical, readers included
    def r(row: Any) -> Any:
        return row["QTY"]

    a = Struct("Item", [Field("qty", T.int, reader=r)])
    env = Env(structs=[a, Struct("Item", [Field("qty", T.int, reader=r)])], item=T.struct("Item"))
    with pytest.raises(ValueError, match="different fields"):
        env.extend(structs=[Struct("Item", [Field("qty", T.int)])])
    with pytest.raises(ValueError, match="different fields"):
        Env(structs=[Struct("Item", [Field("qty", T.int)]), a])


def test_core_rejects_readers_for_unknown_fields() -> None:
    structs = [("S", [("a", "int", None)])]
    with pytest.raises(ValueError, match="unknown struct 'X'"):
        _celspresso.Core(structs, [], [], [], {"X": {"a": len}})
    with pytest.raises(ValueError, match=r"unknown field 'S\.b'"):
        _celspresso.Core(structs, [], [], [], {"S": {"b": len}})


def test_a_failed_build_forgets_its_readers() -> None:
    class Inner:
        pass

    class Outer:
        pass

    class FlakyAdapter:
        """Outer's first build registers Inner (with a reader), then fails."""

        def __init__(self) -> None:
            self.fail = True

        def schema_for(self, tp: Any, ctx: SchemaContext) -> TypeRef | None:
            if tp is Inner:
                return ctx.struct(Inner, lambda: [ctx.field("a", int, reader=lambda o: 1)])
            if tp is not Outer:
                return None

            def build() -> list[Field]:
                fields = [ctx.field("inner", Inner)]
                if self.fail:
                    raise LookupError("schema unavailable")
                return fields

            try:
                return ctx.struct(Outer, build)
            except LookupError:
                self.fail = False
                return ctx.struct(Outer, lambda: [ctx.field("n", int)])

        def decode(self, tp: Any, data: dict[str, Any]) -> Any:
            return data

    env = Env(o=Outer, adapters=[FlakyAdapter()])
    assert env.describe().count("Inner") == 0
    assert env._builder.readers == {}
    # and a later successful registration of Inner gets its reader back
    env2 = env.extend(i=Inner)
    assert set(env2._builder.readers) == {"Inner"}
    assert env2.expr("i.a", int).evaluate({"i": Inner()}) == 1
