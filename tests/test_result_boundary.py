"""A result a rule builds must become a Python value: check_rule proves it meets what
its class's own validation requires, or says it can't."""

import dataclasses
import enum
from typing import Annotated, Literal

import pytest
from pydantic import AfterValidator, BaseModel, ConfigDict, Field, field_validator

from celspresso import Env, RuleCheck, Spec


class Order(BaseModel):
    total: Annotated[int, Field(ge=0, le=100_000)]


def kinds(r: RuleCheck) -> list[str]:
    return [p.kind for p in r.problems]


def check(cls: type, rule: str) -> RuleCheck:
    return Env(o=Order, structs=[cls]).check_rule(rule, Spec(returns=cls))


class Keyed(BaseModel):
    m: Annotated[dict[Literal["a", "b"], int], Field(max_length=2)]


class Flag(BaseModel):
    ok: Literal[True]


class Step(BaseModel):
    n: Annotated[int, Field(multiple_of=5)]


class Tags(BaseModel):
    s: Annotated[set[int], Field(min_length=2, max_length=3)]
    t: set[int]


def test_map_keys_bool_literals_and_multiples_are_checked() -> None:
    assert check(Keyed, "Keyed{m: {'a': 1}}").ok
    r = check(Keyed, "Keyed{m: {'zzz': 1}}")
    assert kinds(r) == ["violates"]
    assert "each key of the result.m is one of" in str(r)
    assert check(Flag, "Flag{ok: o.total >= 0}").ok
    assert "the result.ok is true fails" in str(check(Flag, "Flag{ok: o.total > 0}"))
    assert check(Step, "Step{n: o.total * 5}").ok
    assert "the result.n is a multiple of 5 fails" in str(check(Step, "Step{n: o.total}"))
    # map keys are assumed of inputs too (the other checks never are)
    env = Env(k=Keyed)
    assert env.predicate("'a' in k.m").satisfiable().proved
    assert env.predicate("!('zzz' in k.m)").always_true().proved
    assert env.predicate("k.m.all(x, x.size() == 1)").always_true().proved
    # a multiple_of input isn't assumed, so a witness may break it: reported, not trusted
    assert "fails model validation" in str(Env(s=Step).predicate("s.n == 3").satisfiable())


def test_keys_is_a_public_constraint() -> None:
    from celspresso.schema import Constraints, Field, Struct, T

    def box(tp: T, cons: Constraints) -> Struct:
        return Struct("Box", [Field("m", tp, cons)])

    two = Constraints(max_length=3, keys=Constraints(max_length=2))
    env = Env(b=T.struct("Box"), structs=[box(T.map(T.string, T.int), two)])
    assert env.predicate("b.m.all(k, k.size() <= 2)").always_true().proved
    with pytest.raises(ValueError, match="key"):
        env.compile("b").evaluate({"b": {"m": {"abc": 1}}})
    with pytest.raises(TypeError, match="keys"):
        Env(b=T.struct("Box"), structs=[box(T.int, Constraints(keys=Constraints(max_length=1)))])


def test_what_cant_be_checked_is_unverified_not_accepted() -> None:
    # a set's min_length holds only after duplicates collapse
    r = check(Tags, "Tags{s: [1, 2], t: [1, 1]}")
    assert kinds(r) == ["unverified"]
    assert "a set with min_length" in str(r)

    class Validated(BaseModel):
        n: int

        @field_validator("n")
        @classmethod
        def positive(cls, v: int) -> int:
            if v < 0:
                raise ValueError("negative")
            return v

    r = check(Validated, "Validated{n: o.total}")
    assert kinds(r) == ["unverified"]
    assert "field validators" in str(r)

    class Wrapped(BaseModel):
        n: Annotated[int, AfterValidator(lambda v: v)]

    assert "AfterValidator" in str(check(Wrapped, "Wrapped{n: 1}"))

    @dataclasses.dataclass
    class Posted:
        n: int

        def __post_init__(self) -> None:
            assert self.n >= 0

    assert "__post_init__" in str(check(Posted, "Posted{n: 1}"))


class Color(enum.Enum):
    R = "r"
    G = "g"


class Aliased(BaseModel):
    action: str = Field(alias="Action")


class Strict(BaseModel):
    model_config = ConfigDict(strict=True)
    c: Color


def test_aliased_and_strict_models_decode() -> None:
    env = Env(o=Order, structs=[Aliased, Strict])
    assert env.compile("Aliased{action: 'refund'}").evaluate({"o": {"total": 1}}) == Aliased(Action="refund")
    assert env.compile("Strict{c: 'r'}").evaluate({"o": {"total": 1}}) == Strict(c=Color.R)
    # and a witness for an aliased input decodes too
    v = Env(a=Aliased).predicate("a.action == 'x'").satisfiable()
    assert v.proved
    assert v.witness is not None
    assert v.witness.to_python()["a"] == Aliased(Action="x")
