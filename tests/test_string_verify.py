"""The verifier's string functions: case mapping, int/string conversion, join and split."""

from __future__ import annotations

from typing import Annotated

import pytest
from pydantic import Field

from celspresso import Env, function

env = Env(
    s=Annotated[str, Field(max_length=12)],
    t=str,
    n=int,
    u=Annotated[int, Field(ge=0)],
    xs=Annotated[list[str], Field(max_length=4)],
    b=bool,
)


@pytest.mark.parametrize(
    "src",
    [
        "size(s.upperAscii()) == size(s)",
        "s.lowerAscii().lowerAscii() == s.lowerAscii()",
        "int(string(n)) == n",
        "size(string(n)) <= 20",
        "string(b) == 'true' || string(b) == 'false'",
        "!string(u).startsWith('-')",
        "'ab,c'.split(',') == ['ab', 'c']",
        "['a', 'b'].join('-') == 'a-b'",
        "'Ab1'.upperAscii() == 'AB1'",
    ],
)
def test_proved(src: str) -> None:
    v = env.predicate(src).always_true()
    assert v.proved, v


@pytest.mark.parametrize(
    "src",
    [
        "s.lowerAscii() == s",
        "t.upperAscii() == t",
        "string(n) != '-12'",
        "t.split('aa') != ['', 'a']",  # leftmost matches: 'aaa' splits as ['', 'a']
        "xs.join(',').split(',') == xs",  # [] joins to '' which splits to ['']
        "xs.filter(x, x != '').join('-').size() <= 3",
    ],
)
def test_refuted_with_a_real_counterexample(src: str) -> None:
    p = env.predicate(src)
    v = p.always_true()
    assert v.refuted, v
    assert not p.evaluate(v.counterexample)


def test_int_parsing_accepts_signs_and_leading_zeros() -> None:
    v = env.predicate("int(t) == 7 && t != '7'").satisfiable()
    assert v.sat
    assert v.witness["t"] in ("07", "+7", "007", "+07", "0007")  # whatever the solver picks parses


def test_int_parsing_errors_are_found() -> None:
    v = env.predicate("int(t) > 0").can_error()
    assert v.sat
    with pytest.raises(Exception, match="convert"):
        env.predicate("int(t) > 0").evaluate(v.witness)


def test_split_beyond_the_unroll_limit_is_unknown_not_proved() -> None:
    # 12 characters can split into 13 pieces, more than the 5 slots
    v = env.predicate("s.split(',').size() <= 12").always_true()
    assert v.unknown
    assert v.bounded or "unroll" in v.reason
    wide = Env(s=Annotated[str, Field(max_length=12)], unroll_limit=13)
    assert wide.predicate("s.split(',').size() <= 13").always_true().proved
    assert wide.predicate("s.split(',').size() <= 12").always_true().refuted


def test_cross_case_mapping_is_proved() -> None:
    slow = Env(s=Annotated[str, Field(max_length=12)], timeout=30.0)
    assert slow.predicate("s.upperAscii().lowerAscii() == s.lowerAscii()").always_true().proved


def test_bounds_of_a_split_beyond_the_slots_are_not_exact() -> None:
    # 'a,b,c,d,e,f' has 6 pieces, more than the 5 slots
    b = Env(t=str).expr("size(t.split(','))", int).bounds()
    assert b.bounded
    assert not (b.max and b.max.sound)


def test_a_split_of_each_piece_is_proved_for_bounded_strings() -> None:
    short = Env(s=Annotated[str, Field(max_length=3)])
    v = short.predicate("s.split(',').all(p, p.split('a').size() <= 4)").always_true()
    assert v.proved, v


def test_host_functions_cannot_shadow_builtins_in_another_call_style() -> None:
    @function(name="upperAscii", tabulate=False)
    def ua(x: str) -> str:
        return x + "!"

    with pytest.raises(Exception, match="clashes"):
        Env(s=str).extend(functions=[ua])
