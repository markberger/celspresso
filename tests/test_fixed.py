"""Fixed-point decimals: `T.fixed` and Pydantic `Decimal` with max_digits/decimal_places."""

from __future__ import annotations

import dataclasses
import pickle
from decimal import Decimal
from typing import TYPE_CHECKING, Annotated

import pytest
from pydantic import BaseModel
from pydantic import Field as PField

from celspresso import Env, function
from celspresso.schema import Constraints, Field, Struct, T

if TYPE_CHECKING:
    from celspresso.adapters import SchemaContext

Price = Annotated[Decimal, PField(max_digits=8, decimal_places=2, ge=Decimal(0), le=Decimal("999.99"))]


class Line(BaseModel):
    price: Price
    qty: int


class Order(BaseModel):
    lines: Annotated[list[Line], PField(max_length=3)]
    discount: Annotated[Decimal | None, PField(max_digits=5, decimal_places=2, gt=Decimal("0.005"))] = None


def order(*prices: str) -> Order:
    return Order(lines=[Line(price=Decimal(p), qty=1) for p in prices])


def test_values_are_exact_units_in_cel() -> None:
    env = Env(order=Order)
    assert env.predicate("order.lines[0].price == 1234").evaluate({"order": order("12.34")})
    assert env.predicate("order.lines[0].price == 1200").evaluate({"order": order("12")})
    total = env.expr("order.lines.map(l, l.price).sum()", T.fixed(10, 2))
    assert total.output_type == "fixed(10, 2)"
    got = total.evaluate({"order": order("0.10", "0.20")})
    assert got == Decimal("0.30")
    assert isinstance(got, Decimal)


def test_pydantic_bounds_become_unit_bounds_and_are_proved() -> None:
    env = Env(order=Order)
    assert env.predicate("order.lines.all(l, l.price <= 99999)").always_true().proved
    assert env.predicate("order.lines.exists(l, l.price > 99999)").satisfiable().unsat
    # gt=0.005 with cents is ge 1
    assert env.predicate("order.discount == null || order.discount >= 1").always_true().proved
    assert "fixed(8, 2), >= 0, <= 99999" in env.describe()


def test_witnesses_decode_to_decimals() -> None:
    env = Env(order=Order)
    v = env.predicate("order.lines.exists(l, l.price == 1234)").satisfiable()
    assert v.sat
    o = v.witness.to_python()["order"]
    assert Decimal("12.34") in [line.price for line in o.lines]


def test_digits_bound_the_value() -> None:
    env = Env(x=T.fixed(4, 2))
    assert env.predicate("x <= 9999 && x >= -9999").always_true().proved
    b = env.expr("x", T.fixed(4, 2)).bounds()
    assert (b.min.value, b.max.value) == (Decimal("-99.99"), Decimal("99.99"))


@pytest.mark.parametrize(
    ("value", "err", "match"),
    [
        (Decimal("1.234"), ValueError, "more than 2 decimal places"),
        (Decimal("NaN"), ValueError, "not finite"),
        (Decimal("Infinity"), ValueError, "not finite"),
        (Decimal("1e30"), ValueError, "out of range"),
        (1.5, TypeError, "Decimal"),
        (3, TypeError, "Decimal"),
    ],
)
def test_inexact_or_non_decimal_values_are_rejected(value: object, err: type[Exception], match: str) -> None:
    with pytest.raises(err, match=match) as info:
        Env(x=T.fixed(4, 2)).predicate("x > 0").evaluate({"x": value})
    assert "1.234" not in str(info.value)  # values stay out of messages


def test_trailing_zeros_and_negative_values_convert() -> None:
    p = Env(x=T.fixed(6, 2)).predicate("x == -150")
    assert p.evaluate({"x": Decimal("-1.500")})
    assert not p.evaluate({"x": Decimal("1.5")})


def test_declared_struct_and_nullable_and_lists() -> None:
    item = Struct(
        "Item", [Field("cost", T.fixed(6, 2), Constraints(ge=0)), Field("tip", T.nullable(T.fixed(4, 1)))]
    )
    env = Env(structs=[item], items=T.list(T.struct("Item")), costs=T.list(T.fixed(3, 0)))
    data = {"items": [{"cost": Decimal("1.50"), "tip": None}, {"cost": Decimal(2), "tip": Decimal("0.5")}]}
    assert env.predicate("items.all(i, i.cost >= 150) && items[1].tip == 5").evaluate(data)
    assert env.predicate("costs.all(c, c <= 999)").evaluate({"costs": [Decimal(999)]})
    with pytest.raises(ValueError, match="decimal places"):
        env.predicate("size(costs) > 0").evaluate({"costs": [Decimal("1.5")]})


def test_dataclass_with_pydantic_precision() -> None:
    @dataclasses.dataclass
    class Fee:
        amount: Price

    env = Env(fee=Fee)
    assert env.predicate("fee.amount == 5").evaluate({"fee": Fee(Decimal("0.05"))})


def test_invalid_specs_are_rejected() -> None:
    with pytest.raises(ValueError, match="digits"):
        T.fixed(16, 2)
    with pytest.raises(ValueError, match="digits"):
        T.fixed(3, 4)
    with pytest.raises(ValueError, match="digits"):
        T.fixed(True, 0)  # type: ignore[arg-type]
    with pytest.raises(TypeError, match="map values"):
        T.map(T.string, T.fixed(3, 1))
    with pytest.raises(TypeError, match="map values"):
        Env(m=dict[str, Price])
    with pytest.raises(TypeError, match="fixed precision"):
        Env(x=Decimal)
    with pytest.raises(ValueError, match="digits"):
        Env(x=Annotated[Decimal, PField(max_digits=20, decimal_places=2)])


def test_fixed_cannot_cross_function_boundaries() -> None:
    @function
    def tax(amount: Price) -> int:
        return 0

    with pytest.raises(TypeError, match="function boundary"):
        Env(x=int).extend(functions=[tax])
    with pytest.raises(TypeError, match="function boundary"):
        Env(x=int).define("half", "v / 2", params={"v": T.fixed(4, 2)})


def test_expr_type_check_and_plain_int_results() -> None:
    env = Env(x=T.fixed(4, 2))
    assert env.expr("x + 1", int).evaluate({"x": Decimal("0.01")}) == 2  # raw units
    assert env.expr("x + 1", T.fixed(4, 2)).evaluate({"x": Decimal("0.01")}) == Decimal("0.02")
    with pytest.raises(Exception, match="expected fixed"):
        env.expr("x > 1", T.fixed(4, 2))


def test_typeref_pickles() -> None:
    assert pickle.loads(pickle.dumps(T.fixed(8, 2))) == T.fixed(8, 2)


def test_conversion_is_exact_in_any_decimal_context() -> None:
    import decimal

    st = Struct("Refund", [Field("amount", T.fixed(10, 2), Constraints(le=1234000))])
    env = Env(structs=[st], r=T.struct("Refund"))
    p = env.predicate("r.amount == 1234000")
    with pytest.raises(ValueError, match="decimal places"):  # 29 significant digits, not 12340.00
        p.evaluate({"r": {"amount": Decimal("12340.000000000000000000000001")}})
    with decimal.localcontext() as ctx:
        ctx.prec = 3
        assert p.evaluate({"r": {"amount": Decimal("12340.00")}})
        got = Env(x=T.fixed(10, 2)).expr("x", T.fixed(10, 2)).evaluate({"x": Decimal("12345.67")})
        assert got == Decimal("12345.67")
        assert str(got) == "12345.67"


def test_huge_exponents_fail_fast() -> None:
    import time

    p = Env(x=T.fixed(8, 2)).predicate("x > 0")
    start = time.perf_counter()
    for v in ("1e999990", "1e5000000", "-1e19", "1e-999999"):
        with pytest.raises(ValueError, match=r"out of range|decimal places"):
            p.evaluate({"x": Decimal(v)})
    assert time.perf_counter() - start < 1
    assert Env(x=T.fixed(8, 2)).predicate("x == 0").evaluate({"x": Decimal("0E-50")})
    assert Env(x=T.fixed(8, 2)).predicate("x == 100").evaluate({"x": Decimal("1.000000000")})


def test_witnesses_replay_and_diff_work_on_fixed_values() -> None:
    env = Env(order=Order, x=T.fixed(8, 2))
    p = env.predicate("x > 500 && order.lines.exists(l, l.price == 1234)")
    w = p.satisfiable().witness
    assert p.evaluate(w)
    assert p.explain(w).value is True
    changes = env.predicate("x > 500").diff(env.predicate("x >= 500"))
    assert changes


def test_pydantic_bounds_keep_the_strongest() -> None:
    a = Annotated[Decimal, PField(max_digits=8, decimal_places=2, ge=Decimal("5.001"), gt=Decimal("0.005"))]
    b = Annotated[Decimal, PField(max_digits=8, decimal_places=2, le=Decimal("5.009"), lt=Decimal("100.001"))]
    assert "x: fixed(8, 2), >= 501" in Env(x=a).describe()
    assert "x: fixed(8, 2), <= 500" in Env(x=b).describe()


def test_structs_with_fixed_fields_cannot_cross_function_boundaries() -> None:
    @function
    def tf(line: Line) -> int:
        return 0

    with pytest.raises(TypeError, match="function boundary"):
        Env(x=int).extend(functions=[tf])
    with pytest.raises(TypeError, match="function boundary"):
        Env(x=int).define("p", "l.qty", params={"l": Line})


def test_explicit_constraints_are_in_units() -> None:
    class Fee:
        pass

    class FeeAdapter:
        def schema_for(self, tp: object, ctx: SchemaContext) -> object:
            if tp is not Fee:
                return None
            return ctx.struct(
                tp,
                lambda: [
                    ctx.field(
                        "p", Annotated[Decimal, PField(max_digits=8, decimal_places=2)], Constraints(le=5000)
                    )
                ],
            )

        def decode(self, key: object, data: dict[str, object]) -> object:
            return data

    assert "p: fixed(8, 2), <= 5000" in Env(f=Fee, adapters=[FeeAdapter()]).describe()


def test_expr_identity_includes_the_requested_scale() -> None:
    env = Env(x=T.fixed(8, 2))
    assert env.expr("x", T.fixed(8, 2)) != env.expr("x", T.fixed(8, 4))
    assert env.expr("x", T.fixed(8, 2)) == env.expr("x", T.fixed(8, 2))
    with pytest.raises(TypeError, match="int count of units"):
        env.expr("dyn(1.5)", T.fixed(8, 2)).evaluate({"x": Decimal(1)})


def test_unused_precision_and_decimal_literals() -> None:
    assert Env(i=Annotated[int, PField(max_digits=5)]).predicate("i > 0").evaluate({"i": 3})
    with pytest.raises(TypeError, match="no CEL literal"):
        Env(x=T.fixed(8, 2)).expr("x", T.fixed(8, 2)).gt(Decimal("1.00"))
