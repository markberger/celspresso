"""The verifier's string functions: case mapping, int/string conversion, join and split."""

from __future__ import annotations

from typing import Annotated

import pytest
from pydantic import Field

from celspresso import CelSubsetError, Env, function

env = Env(
    s=Annotated[str, Field(max_length=12)],
    t=str,
    n=int,
    u=Annotated[int, Field(ge=0)],
    xs=Annotated[list[str], Field(max_length=4)],
    ws=Annotated[list[Annotated[str, Field(max_length=3)]], Field(max_length=4)],
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
        "s.split('aa') != ['', 'a']",  # leftmost matches: 'aaa' splits as ['', 'a']
        "ws.join(',').split(',') == ws",  # [] joins to '' which splits to ['']
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
    assert v.proved
    assert v.witness["t"] in ("07", "+7", "007", "+07", "0007")  # whatever the solver picks parses


def test_int_parsing_errors_are_found() -> None:
    v = env.predicate("int(t) > 0").never_errors()
    assert v.refuted
    with pytest.raises(Exception, match="convert"):
        env.predicate("int(t) > 0").evaluate(v.witness)


def test_a_split_gets_a_slot_for_every_piece_it_can_have() -> None:
    # 12 characters can split into 13 pieces, more than a first solve's 5 split slots
    v = env.predicate("s.split(',').size() <= 12").always_true()
    assert v.refuted
    assert env.predicate("s.split(',').size() <= 13").always_true().proved
    assert env.expr("size(s.split(','))", int).bounds().expect() == (1, 13)


def test_a_split_needs_a_bound_on_its_pieces() -> None:
    with pytest.raises(CelSubsetError, match="no max_length"):
        Env(s=str).predicate("s.split(',').size() <= 40")
    with pytest.raises(CelSubsetError, match="up to 101 pieces"):
        Env(s=Annotated[str, Field(max_length=100)]).predicate("s.split(',').size() <= 40")
    # the bound follows concatenation and the pieces of an outer split
    ok = Env(s=Annotated[str, Field(max_length=6)])
    assert ok.predicate("(s + ',' + s + s).split(',').size() <= 20").always_true().proved
    assert ok.predicate("s.split(',').all(p, p.split('a').size() <= 7)").always_true().proved


def test_cross_case_mapping_is_proved() -> None:
    slow = Env(s=Annotated[str, Field(max_length=12)], timeout=30.0)
    assert slow.predicate("s.upperAscii().lowerAscii() == s.lowerAscii()").always_true().proved


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


def test_assumptions_about_split_pieces_are_exact() -> None:
    env = Env(t=Annotated[str, Field(max_length=11)])
    # every piece of a real split is free of the separator, so this assumes nothing
    v = env.predicate("t != 'a,b,c,d'").always_true(assuming="t.split(',').all(p, !p.contains(','))")
    assert v.refuted
    b = env.expr("t.split(',').map(p, p.contains(',') ? 1 / 0 : 1).size()", int).bounds()
    assert b.expect() == (1, 12)


def test_splits_inside_a_comprehension_ignore_slots_that_dont_exist() -> None:
    # dead list slots used to hold unbounded strings, so the split "overflowed" there and
    # the extra-slot retries ended in a timeout
    word = Annotated[str, Field(max_length=4)]
    env = Env(ws=Annotated[list[word], Field(max_length=3)])
    assert env.predicate("ws.all(w, w.split('-').size() <= 5)").always_true().proved
    assert env.predicate("ws.all(w, w.split('-').size() <= 4)").always_true().refuted
