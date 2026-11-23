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
        _celspresso.Core(structs, [], [], [], {"X": ["a"]})
    with pytest.raises(ValueError, match=r"unknown field 'S\.b'"):
        _celspresso.Core(structs, [], [], [], {"S": ["b"]})


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


def _qty_env(reader: Any = None) -> Env:
    item = Struct("Item", [Field("qty", T.int, reader=reader or (lambda row: row["QTY"]))])
    return Env(structs=[item], item=T.struct("Item"))


def test_witnesses_replay_without_readers() -> None:
    env = _qty_env()
    # diff replays each witness through explain; the witness is raw data, not a row
    found = env.predicate("item.qty > 3").diff(env.predicate("item.qty > 5"), limit=3)
    assert found
    assert all(3 < d.witness["item"]["qty"] <= 5 for d in found)
    # check_rule names the runtime error the witness raises
    check = env.check_rule("10 / (item.qty - 3) > 1")
    assert any("division by zero" in p.message for p in check.problems)
    # a Witness can be evaluated directly
    v = env.predicate("item.qty > 3").satisfiable()
    assert v.witness is not None
    assert env.predicate("item.qty > 3").evaluate(v.witness) is True


def test_envs_differing_only_in_readers_are_different() -> None:
    x = _qty_env().predicate("item.qty > 0")
    y = _qty_env(lambda row: -1).predicate("item.qty > 0")
    data = {"item": {"QTY": 1}}
    assert (x.evaluate(data), y.evaluate(data)) == (True, False)
    assert x != y
    with pytest.raises(ValueError, match="different environments"):
        _ = x & y


def test_reader_errors_name_the_field() -> None:
    env = Env(
        structs=[Struct("Item", [Field("qty", T.int, reader=lambda row: row.qty)])],
        items=T.list(T.struct("Item")),
    )
    with pytest.raises(AttributeError) as info:
        env.predicate("items.size() > 0").evaluate({"items": [{"qty": 1}]})
    assert "while reading field 'items[0].qty'" in getattr(info.value, "__notes__", [])


def test_readers_run_once_per_object_for_every_reachable_field() -> None:
    # the documented contract: conversion is eager, whatever the expression reads
    calls: list[int] = []
    item = Struct("Item", [Field("qty", T.int, reader=lambda row: calls.append(1) or row["QTY"])])
    env = Env(structs=[item], items=T.list(T.struct("Item")), n=int)
    env.predicate("n > 0").evaluate({"items": [{"QTY": 1}, {"QTY": 2}], "n": 1})
    assert len(calls) == 2


def test_a_reader_returning_none() -> None:
    item = Struct(
        "Item",
        [
            Field("code", T.nullable(T.string), reader=lambda r: None),
            Field("qty", T.int, reader=lambda r: None),
        ],
    )
    env = Env(structs=[item], item=T.struct("Item"))
    with pytest.raises(TypeError, match=r"expected int at 'item\.qty', got NoneType"):
        env.predicate("item.code == null").evaluate({"item": {}})


def test_reader_cycles_are_collected() -> None:
    import gc
    import weakref

    class Holder:
        env: Env

    def make() -> weakref.ref[Holder]:
        h = Holder()  # h -> env -> reader -> h
        h.env = _qty_env(lambda row: h and row["QTY"])
        h.env.predicate("item.qty > 0").evaluate({"item": {"QTY": 1}})
        return weakref.ref(h)

    ref = make()
    gc.collect()
    assert ref() is None


def test_identically_built_envs_with_adapter_readers_combine() -> None:
    adapter = OrderAdapter()
    a = Env(order=Order, adapters=[adapter]).predicate("order.note == null")
    b = Env(order=Order, adapters=[adapter]).predicate("order.note == null")
    assert a == b
    assert (a & b).evaluate({"order": Order([])})


def test_cli_diff_replays_witnesses_without_readers() -> None:
    from celspresso._cli import RuleFile, run_diff

    env = _qty_env()
    old = RuleFile("old.toml", "", env, {"r": "item.qty > 3"})
    new = RuleFile("new.toml", "", env, {"r": "item.qty > 5"})
    (change,) = run_diff(old, new)
    assert change.status == "changed"
    assert change.examples
    assert all((e.old, e.new) == ("true", "false") for e in change.examples)
