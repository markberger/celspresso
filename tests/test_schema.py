"""celspresso.schema: declaring CEL types directly, without Python classes."""

from __future__ import annotations

import pickle
from dataclasses import dataclass

import pytest

from celspresso import CelEvaluationError, Env
from celspresso.schema import Constraints, Field, Struct, T, TypeRef

ITEM = Struct(
    "shop.Item", [Field("sku", T.string, Constraints(max_length=8)), Field("qty", T.int, Constraints(ge=1))]
)
ORDER = Struct(
    "shop.Order",
    [
        Field("total", T.int, Constraints(ge=0, le=100_000)),
        Field("status", T.string, Constraints(one_of=("new", "paid"))),
        Field("items", T.list(T.struct("shop.Item")), Constraints(max_length=3, items=None)),
        Field("note", T.nullable(T.string)),
        Field("tags", T.map(T.string, T.int)),
    ],
)


def order(**kw: object) -> dict[str, object]:
    base: dict[str, object] = {"total": 10, "status": "new", "items": [], "note": None, "tags": {}}
    return {**base, **kw}


def test_types() -> None:
    assert str(T.list(T.map(T.string, T.nullable(T.int)))) == "list(map(string, int?))"
    assert T.nullable(T.nullable(T.int)) == T.nullable(T.int)
    assert repr(T.struct("shop.Order")) == "TypeRef(shop.Order)"
    assert T.list(T.int) == T.list(T.int) != T.list(T.uint)
    assert hash(T.list(T.int)) == hash(T.list(T.int))
    assert pickle.loads(pickle.dumps(T.map(T.string, T.struct("S")))) == T.map(T.string, T.struct("S"))
    with pytest.raises(AttributeError, match="immutable"):
        T.int._spec = "uint"  # type: ignore[misc]
    with pytest.raises(TypeError, match="expected a TypeRef"):
        T.list(int)  # type: ignore[arg-type]
    for spec in ["integer", ("set", "int"), ["list", "int"], ("list",)]:
        with pytest.raises(TypeError, match="not a CEL type"):
            TypeRef(spec)
    for name in ["", "int", "list(int)", "a b", "map", "Order?", 3]:
        with pytest.raises(ValueError, match="invalid struct name"):
            T.struct(name)  # type: ignore[arg-type]
    assert str(T.struct("Patient@2")) == "Patient@2"


@pytest.mark.parametrize(
    ("kwargs", "error"),
    [
        ({"ge": "1"}, "must be a number"),
        ({"le": True}, "must be a number"),
        ({"max_length": -1}, "non-negative int"),
        ({"pattern": 3}, "must be a str"),
        ({"one_of": ()}, "all-str or all-int"),
        ({"one_of": ("a", 1)}, "all-str or all-int"),
        ({"items": {"ge": 1}}, "must be Constraints"),
        ({"one_of": "abc"}, "list or tuple"),
        ({"one_of": {"a", "b"}}, "list or tuple"),
    ],
)
def test_constraints_are_validated(kwargs: dict[str, object], error: str) -> None:
    with pytest.raises(TypeError, match=error):
        Constraints(**kwargs)  # type: ignore[arg-type]


@pytest.mark.parametrize(
    ("kwargs", "error"),
    [
        ({"ge": float("nan")}, "must be finite"),
        ({"le": float("inf")}, "must be finite"),
        ({"ge": 2**63 - 1}, "not exactly representable"),
        ({"one_of": (2**70,)}, "fit in int64 or uint64"),
    ],
)
def test_constraint_values_are_checked(kwargs: dict[str, object], error: str) -> None:
    with pytest.raises(ValueError, match=error):
        Constraints(**kwargs)  # type: ignore[arg-type]


@pytest.mark.parametrize(
    ("type_", "cons", "error"),
    [
        (T.double, Constraints(one_of=(1, 2)), "one_of with ints applies to int or uint, not double"),
        (T.string, Constraints(one_of=(1, 2)), "one_of with ints"),
        (T.int, Constraints(one_of=("a",)), "one_of with strings applies to string"),
        (T.int, Constraints(pattern="a"), "a pattern applies to string"),
        (T.string, Constraints(ge=1), "a numeric bound"),
        (T.nullable(T.duration), Constraints(ge=1), "a numeric bound"),
        (T.bool, Constraints(lt=1), "a numeric bound"),
        (T.int, Constraints(max_length=3), "a length"),
        (T.string, Constraints(items=Constraints(ge=0)), "items applies to list"),
        (T.list(T.string), Constraints(items=Constraints(ge=0)), r"S\.f\[\]: a numeric bound"),
    ],
)
def test_constraints_must_fit_the_field_type(type_: TypeRef, cons: Constraints, error: str) -> None:
    with pytest.raises(TypeError, match=error):
        Env(structs=[Struct("S", [Field("f", type_, cons)])])


@pytest.mark.parametrize(
    ("type_", "cons", "error"),
    [
        (T.string, Constraints(pattern="("), "invalid pattern"),
        (T.string, Constraints(pattern="(?=a)a"), "invalid pattern"),
        (T.uint, Constraints(le=-1), "no uint satisfies"),
        (T.uint, Constraints(lt=0), "no uint satisfies"),
        (T.uint, Constraints(one_of=(-1, 2)), "non-negative"),
        (T.int, Constraints(one_of=(2**63,)), "fit in int64"),
        (T.int, Constraints(ge=5, le=4), "no value satisfies"),
        (T.double, Constraints(gt=1, le=1), "no value satisfies"),
        (T.double, Constraints(ge=1, lt=1), "no value satisfies"),
        (T.string, Constraints(min_length=3, max_length=2), "exceeds max_length"),
    ],
)
def test_unsatisfiable_or_invalid_constraints_fail_on_declaration(
    type_: TypeRef, cons: Constraints, error: str
) -> None:
    with pytest.raises(ValueError, match=error):
        Env(structs=[Struct("S", [Field("f", type_, cons)])])


def test_constraints_that_fit_are_accepted() -> None:
    fields = [
        Field("a", T.int, Constraints(ge=1, le=1)),
        Field("b", T.uint, Constraints(one_of=(2**64 - 1, 0), le=0)),
        Field("c", T.nullable(T.list(T.string)), Constraints(max_length=2, items=Constraints(pattern="^x"))),
        Field("d", T.map(T.string, T.int), Constraints(min_length=1)),
        Field("e", T.bytes, Constraints(max_length=4)),
    ]
    env = Env(structs=[Struct("S", fields)], s=T.struct("S"))
    assert env.predicate("s.a == 1").always_true().proved
    assert env.predicate("s.c == null || size(s.c) <= 2").always_true().proved


def test_struct_and_field_validation() -> None:
    assert Constraints(one_of=["a", "b"]).one_of == ("a", "b")  # type: ignore[arg-type]
    with pytest.raises(ValueError, match="invalid field name"):
        Field("not a name", T.int)
    with pytest.raises(TypeError, match="field 'x'"):
        Field("x", int)  # type: ignore[arg-type]
    with pytest.raises(TypeError, match="must be Constraints"):
        Field("x", T.int, {"ge": 0})  # type: ignore[arg-type]
    with pytest.raises(ValueError, match="declared twice"):
        Struct("S", [Field("a", T.int), Field("a", T.string)])
    with pytest.raises(TypeError, match="expected Field values"):
        Struct("S", ["a"])  # type: ignore[list-item]
    with pytest.raises(ValueError, match="invalid struct name"):
        Struct("", [])


def test_declared_structs_check_evaluate_and_verify() -> None:
    env = Env(structs=[ITEM, ORDER], order=T.struct("shop.Order"))
    assert env.variables == {"order": "shop.Order"}
    # constraints are facts for the prover...
    assert env.predicate("order.total < 0 || order.status == 'gold'").satisfiable().unsat
    assert env.predicate("size(order.items) <= 3").always_true().proved
    v = env.predicate("order.items.all(i, i.qty <= 5)").always_true()
    assert v.refuted
    assert v.counterexample is not None
    witness = v.counterexample.to_python()["order"]
    assert isinstance(witness, dict)  # no class to rebuild: values come back as dicts
    assert any(i["qty"] > 5 for i in witness["items"])
    # ...and enforced on evaluation
    p = env.predicate("order.total > 5 && !has(order.note)")
    assert p.evaluate({"order": order(total=6)})
    with pytest.raises(ValueError, match=r"input 'order.items\[0\].sku' violates the schema"):
        p.evaluate({"order": order(items=[{"sku": "too-long-sku", "qty": 1}])})
    with pytest.raises(CelEvaluationError):
        env.expr("order.tags['missing']", int).evaluate({"order": order()})

    # values may also be objects with attributes (an ORM row, say)
    @dataclass
    class Row:
        total: int
        status: str
        items: list[object]
        note: str | None
        tags: dict[str, int]

    assert p.evaluate({"order": Row(6, "paid", [], None, {})})
    assert env.expr("order", T.struct("shop.Order")).evaluate({"order": order()}) == order()
    assert "shop.Item\n    sku: string, size <= 8\n    qty: int, >= 1" in env.describe()


def test_two_versions_of_a_struct_in_one_env() -> None:
    # e.g. a model before and after a migration that moved `phone` into `contact`
    v1 = Struct("Patient@1", [Field("phone", T.string)])
    contact = Struct("Contact@2", [Field("phone", T.string)])
    v2 = Struct("Patient@2", [Field("contact", T.struct("Contact@2"))])
    env = Env(structs=[v1, contact, v2], old=T.struct("Patient@1"), new=T.struct("Patient@2"))
    env = env.define("display", "p.startsWith('+1') ? p.substring(2) : p", params={"p": T.string})
    same = env.predicate("display(old.phone) == display(new.contact.phone)")
    assert same.always_true(assuming="new.contact.phone == old.phone").proved
    assert same.always_true().refuted


def test_declarations_must_agree() -> None:
    env = Env(structs=[ITEM])
    assert env.extend(structs=[ITEM], item=T.struct("shop.Item")).variables == {"item": "shop.Item"}
    other_item = Struct("shop.Item", [Field("sku", T.string)])
    with pytest.raises(ValueError, match="already declared with different fields"):
        env.extend(structs=[other_item])
    with pytest.raises(TypeError, match=r"unknown struct 'shop\.Item'"):
        Env(order=T.struct("shop.Item"))
    with pytest.raises(TypeError, match=r"shop.Order.items: unknown struct 'shop.Item'"):
        Env(structs=[ORDER])
    with pytest.raises(TypeError, match=r"expects celspresso\.schema\.Struct"):
        Env(structs=[{"name": "x"}])  # type: ignore[list-item]
    with pytest.raises(TypeError, match="'structs' is an Env option"):
        Env(structs=ITEM)  # type: ignore[arg-type]
    with pytest.raises(TypeError, match="'structs' is an Env option"):
        env.extend(structs=T.int)  # type: ignore[arg-type]
    assert Env({"structs": int}).variables == {"structs": "int"}


def test_declared_structs_and_classes_share_one_namespace() -> None:
    @dataclass
    class Item:
        name: str

    # a class whose name a declared struct already holds gets a qualified one...
    env = Env(structs=[Struct("Item", [Field("sku", T.string)])], declared=T.struct("Item"), cls=Item)
    assert env.variables["declared"] == "Item"
    assert env.variables["cls"] != "Item"
    assert env.predicate("declared.sku == cls.name").satisfiable().sat
    # ...and a declared struct can't take a name a class holds
    with pytest.raises(ValueError, match="already used by"):
        Env(x=Item).extend(structs=[Struct("Item", [Field("name", T.string)])])
    # nor refer to a class's struct by name: that name depends on registration order
    with pytest.raises(TypeError, match="use that type itself"):
        Env(x=Item).extend(structs=[Struct("Box", [Field("i", T.struct("Item"))])])
    with pytest.raises(TypeError, match="use that type itself"):
        Env(x=Item).extend(y=T.struct("Item"))


def test_envs_with_different_structs_of_one_name_are_different() -> None:
    a = Env(structs=[Struct("S", [Field("a", T.int)])], s=T.struct("S"))
    b = Env(structs=[Struct("S", [Field("b", T.int)])], s=T.struct("S"))
    with pytest.raises(ValueError, match="different environments"):
        a.predicate("s.a > 0") & b.predicate("s.b > 0")


def test_a_class_and_a_declared_struct_with_equal_fields_are_different() -> None:
    @dataclass
    class P:
        v: int

    by_class = Env(o=P)
    declared = Env(structs=[Struct("P", [Field("v", T.int)])], o=T.struct("P"))
    assert by_class.variables == declared.variables
    assert by_class.predicate("o.v > 1") != declared.predicate("o.v > 1")
    with pytest.raises(ValueError, match="different environments"):
        by_class.predicate("o.v > 1") & declared.predicate("o.v < 5")
