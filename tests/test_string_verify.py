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


def test_split_of_a_bounded_string_gets_enough_slots() -> None:
    # 12 characters can split into 13 pieces, more than the 5 slots: more are added
    v = env.predicate("s.split(',').size() <= 12").always_true()
    assert v.refuted
    assert env.predicate("s.split(',').size() <= 13").always_true().proved


def test_split_of_an_unbounded_string_is_unknown_not_proved() -> None:
    v = Env(s=str).predicate("s.split(',').size() <= 40").always_true()
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


def test_host_overloads_on_builtin_names_run_only_for_their_own_calls() -> None:
    @function(name="upperAscii", tabulate=False)
    def shout(x: str) -> str:
        return x + "!"

    @function(name="size", tabulate=False)
    def size_of_int(n: int) -> int:
        return n

    env = Env(s=str, n=int).extend(functions=[shout, size_of_int])
    for src in ["size(s.upperAscii()) == size(s)", "[1, 2].size() == 2", "size(s) >= 0"]:
        p = env.predicate(src)
        assert p.always_true().proved
        assert p.evaluate({"s": "ab", "n": 0})
    # the host overloads themselves still run, and are opaque to the verifier
    assert env.expr("upperAscii(s)", str).evaluate({"s": "a", "n": 0}) == "a!"
    assert env.expr("size(n)", int).evaluate({"s": "", "n": 4}) == 4
    assert env.predicate("upperAscii(s) == s.upperAscii()").always_true().refuted


def test_assumptions_about_split_pieces_cannot_hide_an_overflow() -> None:
    # true of every t, but false of the encoding's truncated last piece
    env = Env(t=str)
    v = env.predicate("t != 'a,b,c,d,e,f'").always_true(assuming="t.split(',').all(p, !p.contains(','))")
    assert not v.proved
    b = env.expr("t.split(',').map(p, p.contains(',') ? 1 / 0 : 1).size()", int).bounds()
    assert b.bounded
    assert not (b.max and b.max.sound)
