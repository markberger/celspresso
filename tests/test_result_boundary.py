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


def test_review_round_one_cases_are_unverified_or_checked() -> None:
    import decimal

    import annotated_types as at
    from pydantic import GetPydanticSchema, StringConstraints
    from pydantic_core import core_schema

    class Cents(BaseModel):
        d: Annotated[decimal.Decimal, Field(max_digits=6, decimal_places=2, multiple_of=5)]

    class Nickel(BaseModel):
        d: Annotated[
            decimal.Decimal, Field(max_digits=6, decimal_places=2, multiple_of=decimal.Decimal("0.05"))
        ]

    # 5 means 5.00, i.e. 500 units; 0.05 is 5 units
    assert "multiple of 500" in str(check(Cents, "Cents{d: 100}"))
    assert check(Cents, "Cents{d: 500}").ok
    assert check(Nickel, "Nickel{d: o.total * 5}").ok
    assert "multiple of 5 fails" in str(check(Nickel, "Nickel{d: 101}"))

    class Pred(BaseModel):
        n: Annotated[int, at.Predicate(lambda v: v > 10)]

    class Schemed(BaseModel):
        n: Annotated[
            int, GetPydanticSchema(lambda t, h: core_schema.no_info_after_validator_function(int, h(t)))
        ]

    class Stripped(BaseModel):
        s: Annotated[str, StringConstraints(strip_whitespace=True, min_length=1)]

    class Short(BaseModel):
        model_config = ConfigDict(str_max_length=2)
        s: str

    class Posted(BaseModel):
        n: int

        def model_post_init(self, context: object) -> None:
            raise ValueError("no")

    for cls, rule, why in [
        (Pred, "Pred{n: 1}", "Predicate"),
        (Schemed, "Schemed{n: 1}", "GetPydanticSchema"),
        (Stripped, "Stripped{s: ' '}", "strip_whitespace"),
        (Short, "Short{s: 'abc'}", "str_max_length"),
        (Posted, "Posted{n: 1}", "model_post_init"),
    ]:
        r = check(cls, rule)
        assert kinds(r) == ["unverified"], (cls, str(r))
        assert why in str(r)

    class Private(BaseModel):  # private attributes alone don't make a model unverifiable
        n: int
        _cache: int = 0

    assert check(Private, "Private{n: 1}").ok


def test_celspresso_constraints_as_metadata_keep_keys() -> None:
    from celspresso.schema import Constraints

    @dataclasses.dataclass
    class Bag:
        m: Annotated[dict[str, int], Constraints(max_length=2, keys=Constraints(one_of=("a", "b")))]

    env = Env(b=Bag)
    assert env.predicate("!('z' in b.m)").always_true().proved
    assert "each key of the result.m" in str(
        Env(structs=[Bag]).check_rule("Bag{m: {'z': 1}}", Spec(returns=Bag))
    )


def test_review_round_two_cases() -> None:
    import re

    import pydantic.dataclasses as pdc
    from pydantic import conint

    class Con(BaseModel):  # conint's None placeholders aren't unmodelled metadata
        n: conint(ge=0, le=10)  # type: ignore[valid-type]
        d: Annotated[int, "a doc string"]

    assert check(Con, "Con{n: 3, d: 1}").ok

    @pdc.dataclass
    class PD:
        s: str

    @pdc.dataclass(config=ConfigDict(str_to_lower=True))
    class Lower:
        s: str

    assert check(PD, "PD{s: 'a'}").ok
    assert "str_to_lower" in str(check(Lower, "Lower{s: 'ABC'}"))

    @dataclasses.dataclass(init=False)
    class OwnInit:
        n: int

        def __init__(self, n: int) -> None:
            self.n = n * 2

    @dataclasses.dataclass
    class Later:
        n: int
        m: int = dataclasses.field(default=7, init=False)

    class Flagged(BaseModel):
        s: Annotated[str, Field(pattern=re.compile("abc", re.I))]

    class Hooked(BaseModel):
        n: int

        @classmethod
        def model_validate(cls, *a: object, **k: object) -> "Hooked":  # type: ignore[override]
            return cls(n=2)

    for cls, rule, why in [
        (OwnInit, "OwnInit{n: 3}", "__init__"),
        (Later, "Later{n: 1, m: 99}", "init=False"),
        (Flagged, "Flagged{s: 'abc'}", "pattern"),
        (Hooked, "Hooked{n: 1}", "model_validate"),
    ]:
        r = check(cls, rule)
        assert kinds(r) == ["unverified"], (cls, str(r))
        assert why in str(r)
    # a compiled pattern isn't assumed of inputs (Pydantic runs it with Python's flags)
    assert "fails model validation" in str(Env(f=Flagged).predicate("f.s == 'x'").satisfiable())

    class Inner(BaseModel):
        model_config = ConfigDict(frozen=True)
        k: int

    class Uniq(BaseModel):
        s: Annotated[frozenset[Inner], Field(max_length=3)]

    assert check(Uniq, "Uniq{s: [Inner{k: 1}, Inner{k: 2}]}").ok
    assert "has no duplicates" in str(check(Uniq, "Uniq{s: [Inner{k: 1}, Inner{k: 1}]}"))
