"""The strict profile: by default an Env accepts only what the verifier decides exactly."""

from __future__ import annotations

from typing import Annotated

import pytest
from pydantic import BaseModel, Field

from celspresso import CelTypeError, Env, function

Name = Annotated[str, Field(max_length=20)]


def test_envs_are_strict_by_default() -> None:
    env = Env(s=Name, d=float)
    with pytest.raises(CelTypeError) as exc:
        env.compile("string(d) + s")
    message = str(exc.value)
    assert "outside the strict profile" in message
    assert "fixed-point" in message  # says what to use instead
    assert "strict=False" in message
    assert "^^^^^^^^^" in message  # points at the call


def test_strict_false_accepts_all_of_cel() -> None:
    env = Env(s=Name, d=float, strict=False)
    assert env.compile("string(d) + s").evaluate({"d": 1.5, "s": "x"}) == "1.5x"
    assert env.predicate("[3, 1].sort() == [1, 3]").evaluate({"d": 0.0, "s": ""}) is True


def test_every_error_is_reported() -> None:
    with pytest.raises(CelTypeError) as exc:
        Env(s=Name).compile("s.split(s).size() + size(b'ab')")
    assert "3 errors" in str(exc.value)
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
def test_formatting_logic_is_inside_the_profile(src: str) -> None:
    Env(s=Name, n=int).compile(src)


def test_derived_envs_keep_the_profile() -> None:
    strict = Env(s=Name).define("t", "s + '!'").extend(assumptions=["size(s) > 0"])
    loose = Env(s=Name, strict=False).define("t", "s + '!'")
    with pytest.raises(CelTypeError):
        strict.compile("t.reverse()")
    assert loose.compile("t.reverse()").evaluate({"s": "ab"}) == "!ba"
    with pytest.raises(CelTypeError, match="outside the strict profile"):
        Env(s=Name).define("u", "s.reverse()")


def test_combinators_stay_inside_the_profile() -> None:
    env = Env(s=Name)
    with pytest.raises(CelTypeError):
        _ = env.predicate("s == ''") & "s.trim() == ''"


def test_strict_is_an_option_not_a_variable() -> None:
    with pytest.raises(TypeError, match="'strict' is an Env option"):
        Env(strict=int)  # type: ignore[arg-type]
    assert Env({"strict": int}).variables == {"strict": "int"}


class Blob(BaseModel):
    data: bytes


@pytest.mark.parametrize("src", ["b == c", "b in [c]", "[b] == [c]", "p.data == b", "size([b]) == 1"])
def test_bytes_values_are_outside_the_profile(src: str) -> None:
    with pytest.raises(CelTypeError, match="bytes values are outside the strict profile"):
        Env(b=bytes, c=bytes, p=Blob).compile(src)


def test_contracts_and_parameterized_definitions_are_checked() -> None:
    @function(ensures="result == s.reverse()")
    def g(s: str) -> str:
        return s[::-1]

    with pytest.raises(CelTypeError, match="outside the strict profile"):
        Env(s=Name).extend(functions=[g])
    with pytest.raises(CelTypeError, match="outside the strict profile"):
        Env(s=Name).define("f", "v.reverse()", params={"v": str})
    loose = Env(s=Name, strict=False).extend(functions=[g]).define("f", "v.reverse()", params={"v": str})
    assert loose.compile("f(s) + g(s)").evaluate({"s": "ab"}) == "baba"


def test_a_strict_env_refuses_expressions_from_a_loose_one() -> None:
    loose = Env(s=Name, strict=False).predicate("s.reverse() == s")
    with pytest.raises(ValueError, match="different environments"):
        Env(s=Name).predicate("s == s").equivalent(loose)


def test_host_functions_stay_allowed_even_on_builtin_names() -> None:
    @function(name="contains")
    def contains_n(s: str, n: int) -> bool:
        return str(n) in s

    @function
    def reverse(s: str) -> str:
        return s[::-1]

    env = Env(s=Name, n=int).extend(functions=[contains_n, reverse])
    assert env.predicate("contains(s, n) && reverse(s) == s").evaluate({"s": "1", "n": 1}) is True
    with pytest.raises(CelTypeError, match="outside the strict profile"):
        env.compile("s.reverse()")  # the builtin receiver form is still the builtin


class Person(BaseModel):
    nick: str | None = None


def test_optionals_and_presence_are_inside_the_profile() -> None:
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


def test_structs_holding_bytes_are_outside_the_profile() -> None:
    with pytest.raises(CelTypeError, match="bytes values"):
        Env(p=Pair, q=Pair).compile("p.name != q.name || p == q")
    Env(p=Pair).compile("p.name == 'x'")  # reading other fields is fine


def test_host_functions_may_start_with_an_underscore() -> None:
    @function
    def _clean(x: str) -> str:
        return x.strip()

    assert Env(s=Name).extend(functions=[_clean]).predicate("_clean(s) == s").evaluate({"s": "a"}) is True


def test_schema_patterns_must_be_in_the_profile() -> None:
    slow = Annotated[str, Field(pattern=r"^\w+@\w+$", max_length=20)]
    with pytest.raises(ValueError, match="pattern on 'z' is outside the strict profile"):
        Env(z=slow)
    Env(z=slow, strict=False)
    with pytest.raises(ValueError, match="pattern on 'zs'"):
        Env(zs=list[slow])
    Env(z=Annotated[str, Field(pattern=r"^[A-Za-z0-9_]+@[a-z]+$", max_length=20)])


def test_pattern_errors_point_at_the_pattern() -> None:
    with pytest.raises(CelTypeError) as exc:
        Env(s=Name).compile("s.matches('[')")
    assert "\n  |           ^^^" in str(exc.value)
