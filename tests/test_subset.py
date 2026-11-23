"""celspresso's CEL subset: an Env accepts only what the verifier decides exactly and quickly."""

from __future__ import annotations

from typing import Annotated, Any

import pytest
from pydantic import BaseModel, Field

from celspresso import CelTypeError, Env, function

Name = Annotated[str, Field(max_length=20)]


def test_outside_the_subset_is_a_compile_error_with_a_reason() -> None:
    env = Env(s=Name, n=int)
    with pytest.raises(CelTypeError) as exc:
        env.compile("[s].sort()[0] + s")
    message = str(exc.value)
    assert "not part of celspresso's CEL subset" in message
    assert "strict" not in message  # there is no opt-out to suggest
    assert "^^^^" in message  # points at the call


def test_every_error_is_reported() -> None:
    with pytest.raises(CelTypeError) as exc:
        Env(s=Name).compile("s.split(s).size() + size(b'ab')")
    assert "2 errors" in str(exc.value)
    assert "literal, non-empty separator" in str(exc.value)


@pytest.mark.parametrize(
    "src",
    [
        "s.startsWith('A') ? s.upperAscii() : s.substring(0, 1)",
        "[s, 'x'].join(' ') == s + ' x'",
        "s.matches('^[A-Z]+$') && s.split('-').size() == 2",
        "(n < 10 ? '0' : '') + string(n) == '07'",
        "int(s) > 3 && math.greatest(n, 2) == n",
    ],
)
def test_formatting_logic_is_inside_the_subset(src: str) -> None:
    Env(s=Name, n=int).compile(src)


def test_derived_envs_keep_the_subset() -> None:
    env = Env(s=Name).define("t", "s + '!'").extend(assumptions=["size(s) > 0"])
    with pytest.raises(CelTypeError):
        env.compile("t.reverse()")
    with pytest.raises(CelTypeError, match="not part of celspresso's CEL subset"):
        Env(s=Name).define("u", "s.reverse()")


def test_combinators_stay_inside_the_subset() -> None:
    env = Env(s=Name)
    with pytest.raises(CelTypeError):
        _ = env.predicate("s == ''") & "s.trim() == ''"


def test_strict_is_no_longer_an_option() -> None:
    with pytest.raises(TypeError):
        Env(strict=False)  # type: ignore[arg-type]
    assert Env({"strict": int}).variables == {"strict": "int"}


@pytest.mark.parametrize(
    "src", ["d < 2", "n < 2.5", "[1.5].size() == 1", "double(n) > 0.0", "string(d) == '1.5'", "p.ratio > 0.5"]
)
def test_doubles_are_outside_the_subset(src: str) -> None:
    class Ratio(BaseModel):
        ratio: float
        name: str

    with pytest.raises(CelTypeError, match="fixed-point"):
        Env(d=float, n=int, p=Ratio).compile(src)


def test_structs_with_a_double_field_can_still_be_read_through() -> None:
    class Ratio(BaseModel):
        ratio: float
        name: str

    assert Env(p=Ratio).predicate("p.name == 'x'").evaluate({"p": Ratio(ratio=0.5, name="x")}) is True


class Blob(BaseModel):
    data: bytes


@pytest.mark.parametrize("src", ["b == c", "b in [c]", "[b] == [c]", "p.data == b", "size([b]) == 1"])
def test_bytes_values_are_outside_the_subset(src: str) -> None:
    with pytest.raises(CelTypeError, match="bytes values are not part"):
        Env(b=bytes, c=bytes, p=Blob).compile(src)


def test_contracts_and_parameterized_definitions_are_checked() -> None:
    @function(ensures="result == s.reverse()")
    def g(s: str) -> str:
        return s[::-1]

    with pytest.raises(CelTypeError, match="not part of celspresso's CEL subset"):
        Env(s=Name).extend(functions=[g])
    with pytest.raises(CelTypeError, match="not part of celspresso's CEL subset"):
        Env(s=Name).define("f", "v.reverse()", params={"v": str})


def test_host_functions_stay_allowed_even_on_builtin_names() -> None:
    @function(name="contains")
    def contains_n(s: str, n: int) -> bool:
        return str(n) in s

    @function
    def reverse(s: str) -> str:
        return s[::-1]

    env = Env(s=Name, n=int).extend(functions=[contains_n, reverse])
    assert env.predicate("contains(s, n) && reverse(s) == s").evaluate({"s": "1", "n": 1}) is True
    with pytest.raises(CelTypeError, match="not part of celspresso's CEL subset"):
        env.compile("s.reverse()")  # the builtin receiver form is still the builtin


class Person(BaseModel):
    nick: str | None = None


def test_optionals_and_presence_are_inside_the_subset() -> None:
    env = Env(p=Person, m=dict[str, int], xs=list[int])
    env.compile("p.?nick.orValue('') + string(m[?'k'].orValue(0)) + string(xs[?0].orValue(1))")
    env.compile("has(p.nick) && 'k' in m")
    env.compile("[?m[?'a'], 3] == [3] && {?'k': m[?'a']} == {}")


@pytest.mark.parametrize(
    ("src", "hint"),
    [
        (r"s.matches(r'^\d{5}$')", "[0-9]"),
        ("s.matches('a(?=b)')", "invalid pattern"),
        ("s.matches('[')", "invalid"),
    ],
)
def test_patterns_must_be_ones_the_verifier_solves_quickly(src: str, hint: str) -> None:
    with pytest.raises(CelTypeError, match="pattern") as exc:
        Env(s=Name).compile(src)
    assert hint in str(exc.value)


class Pair(BaseModel):
    data: bytes
    name: str


def test_structs_holding_bytes_are_outside_the_subset() -> None:
    with pytest.raises(CelTypeError, match="bytes values"):
        Env(p=Pair, q=Pair).compile("p.name != q.name || p == q")
    Env(p=Pair).compile("p.name == 'x'")  # reading other fields is fine


def test_host_functions_may_start_with_an_underscore() -> None:
    @function
    def _clean(x: str) -> str:
        return x.strip()

    assert Env(s=Name).extend(functions=[_clean]).predicate("_clean(s) == s").evaluate({"s": "a"}) is True


def test_schema_patterns_must_be_in_the_subset() -> None:
    slow = Annotated[str, Field(pattern=r"^\w+@\w+$", max_length=20)]
    with pytest.raises(ValueError, match="pattern on 'z' is outside celspresso's CEL subset"):
        Env(z=slow)
    with pytest.raises(ValueError, match="pattern on 'zs'"):
        Env(zs=list[slow])
    Env(z=Annotated[str, Field(pattern=r"^[A-Za-z0-9_]+@[a-z]+$", max_length=20)])


def test_pattern_errors_point_at_the_pattern() -> None:
    with pytest.raises(CelTypeError) as exc:
        Env(s=Name).compile("s.matches('[')")
    assert "\n  |           ^^^" in str(exc.value)


class Reading(BaseModel):
    ratio: float
    name: str
    age: int
    nick: str | None = None


@pytest.mark.parametrize(
    "src",
    [
        "has(p.name)",
        "p.?nick.orValue('') == ''",
        "ps.exists(q, q.name == 'x')",
        "ps[0].age > 1",
        "p.name == q.name",
    ],
)
def test_structs_with_an_unused_double_field_stay_usable(src: str) -> None:
    Env(p=Reading, q=Reading, ps=Annotated[list[Reading], Field(max_length=3)]).compile(src)


def test_comparing_whole_structs_with_a_double_field_is_rejected_once() -> None:
    with pytest.raises(CelTypeError, match="compare the fields you need") as exc:
        Env(p=Reading, q=Reading).compile("p == q")
    assert "1 error" in str(exc.value)


@pytest.mark.parametrize(
    ("src", "hint"),
    [
        ("[1, 'a'][0] == 1", "unknown type"),
        ("{'a': 1, 'b': 'x'}['a'] == 1", "unknown type"),
        ("dm['k'] == 1", "unknown type"),
        ("anyf(n) == 1", "unknown type"),
        ("half(n) == half(m)", "fixed-point"),
        ("int(half(n)) == n", "fixed-point"),
        ("double(n) > 1.0", "fixed-point"),
    ],
)
def test_dyn_and_double_values_from_any_source_are_rejected(src: str, hint: str) -> None:
    @function
    def half(n: int) -> float:
        return n / 2

    @function
    def anyf(n: int) -> Any:
        return n

    env = Env(n=int, m=int, dm=dict[str, Any]).extend(functions=[half, anyf])
    with pytest.raises(CelTypeError, match=hint):
        env.compile(src)
    assert env.predicate("'k' in dm && size(dm) > 0").evaluate({"n": 0, "m": 0, "dm": {"k": 1}}) is True
