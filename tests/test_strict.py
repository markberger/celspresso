"""The strict profile: by default an Env accepts only what the verifier decides exactly."""

from __future__ import annotations

from typing import Annotated

import pytest
from pydantic import Field

from celspresso import CelTypeError, Env

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
