"""The CEL language surface beyond the core: time types, type values, macros, extensions."""

from __future__ import annotations

import datetime as dt

import pytest
from pydantic import BaseModel

from celspresso import CelEvaluationError, CelTypeError, Env
from celspresso._types import cel_literal

UTC = dt.timezone.utc


class Session(BaseModel):
    started: dt.datetime
    idle: dt.timedelta


ENV = Env(s=Session, now=dt.datetime)
SESSION = Session(started=dt.datetime(2026, 11, 21, 9, tzinfo=UTC), idle=dt.timedelta(minutes=3))


def run(src: str, now: dt.datetime | None = None) -> object:
    return ENV.compile(src).evaluate({"s": SESSION, "now": now or SESSION.started})


def test_timestamp_and_duration_arithmetic() -> None:
    expired = ENV.predicate("now - s.started > duration('8h') || s.idle > duration('15m')")
    assert expired.evaluate({"s": SESSION, "now": dt.datetime(2026, 11, 21, 18, tzinfo=UTC)})
    assert not expired.evaluate({"s": SESSION, "now": dt.datetime(2026, 11, 21, 10, tzinfo=UTC)})


def test_time_values_round_trip_to_python() -> None:
    assert ENV.expr("s.started + s.idle", dt.datetime).evaluate(
        {"s": SESSION, "now": SESSION.started}
    ) == dt.datetime(2026, 11, 21, 9, 3, tzinfo=UTC)
    assert run("now - s.started") == dt.timedelta(0)
    assert run("duration('-1.5s')") == dt.timedelta(seconds=-1.5)
    # non-UTC input is normalized to the same instant
    plus2 = dt.timezone(dt.timedelta(hours=2))
    assert (
        run("now == timestamp('2026-11-21T09:00:00Z')", dt.datetime(2026, 11, 21, 11, tzinfo=plus2)) is True
    )


def test_timestamp_accessors_and_time_zones() -> None:
    assert run("s.started.getHours()") == 9
    assert run("s.started.getDayOfWeek()") == 6  # a Saturday
    with pytest.raises(CelTypeError, match="time zones are not modeled"):
        ENV.compile("s.started.getHours('America/New_York')")


def test_naive_datetimes_are_rejected() -> None:
    with pytest.raises(ValueError, match="naive datetime"):
        run("true", dt.datetime(2026, 1, 1))
    with pytest.raises(TypeError, match="naive datetime"):
        cel_literal(dt.datetime(2026, 1, 1))


def test_time_literals() -> None:
    assert cel_literal(dt.datetime(2026, 1, 2, 3, 4, 5, tzinfo=UTC)) == 'timestamp("2026-01-02T03:04:05Z")'
    assert cel_literal(dt.timedelta(seconds=-90, microseconds=5)) == 'duration("-89s999995us")'
    assert run(cel_literal(dt.timedelta(seconds=-90, microseconds=5))) == dt.timedelta(
        seconds=-90, microseconds=5
    )


def test_out_of_range_time_is_an_error() -> None:
    with pytest.raises(CelEvaluationError, match="out of range"):
        run("timestamp('9999-12-31T23:59:59Z') + duration('1s')")


def test_two_variable_macros_and_bind() -> None:
    assert run("[10, 20].all(i, v, v == (i + 1) * 10)") is True
    assert run("{'a': 1, 'b': 2}.transformMap(k, v, v * 10)") == {"a": 10, "b": 20}
    assert run("[1, 2, 3].transformList(i, v, i > 0, v * v)") == [4, 9]
    assert run("cel.bind(x, 6, x * x)") == 36
    source = ENV.compile("cel.bind(x, 6, x * x) == [1].transformList(i, v, v)[0]").source
    assert "cel.bind(x, 6, x * x)" in source


def test_extension_libraries() -> None:
    assert run("math.greatest(1, 3, 2)") == 3
    assert run("math.least([3, 1, 2])") == 1
    assert run("'a,b,c'.split(',').join('-')") == "a-b-c"
    for src in ["[3, 1, 2].sort()", "sets.contains([1, 2, 3], [3, 1])", "base64.encode(b'hi')"]:
        with pytest.raises(CelTypeError, match="not part of celspresso's CEL subset"):
            ENV.compile(src)


def test_namespaces_do_not_shadow_variables() -> None:
    # a variable named `math` keeps its meaning; math.greatest is then a field access
    env = Env(math=dict[str, int])
    assert env.compile("math.greatest").evaluate({"math": {"greatest": 7}}) == 7
    with pytest.raises(CelTypeError):
        env.compile("math.greatest('a')")


def test_optionals() -> None:
    env = Env(m=dict[str, int])
    assert env.compile("m.?a.orValue(0)").evaluate({"m": {"a": 5}}) == 5
    assert env.compile("m.?b.orValue(0)").evaluate({"m": {}}) == 0
    assert env.compile("[?m.?a, ?m.?b, 3]").evaluate({"m": {"a": 1}}) == [1, 3]
    assert env.compile("{?'x': m.?a}").evaluate({"m": {}}) == {}
    assert (
        env.compile("m.?a.optMap(v, v * 2)").evaluate({"m": {"a": 4}}) == 8
    )  # present optional -> its value
    assert env.compile("m.?a").evaluate({"m": {}}) is None  # absent optional -> None
    assert env.expr("m.?a", int).output_type == "optional_type(int)"
    with pytest.raises(CelEvaluationError, match=r"optional\.none"):
        env.compile("m.?a.value()").evaluate({"m": {}})
    assert env.compile("m.?a.optMap(v, v + 1)").source == "m.?a.optMap(v, v + 1)"


def test_the_verifier_reasons_about_optionals_and_maps() -> None:
    env = Env(m=dict[str, int])
    v = env.predicate("m.?a.orValue(0) >= 0").always_true()
    assert v.refuted
    assert v.counterexample == {"m": {"a": -1}} or v.counterexample["m"]["a"] < 0
    assert env.predicate("m.?a.orValue(1) >= 1 || m.a < 1").always_true().unknown  # m is unbounded


def test_block() -> None:
    assert run("cel.block([2, cel.index(0) * 3], cel.index(1) + 1)") == 7
