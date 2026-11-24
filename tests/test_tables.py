"""Decision tables: first-match rows, checked for gaps, dead rows, overlaps, and as a rule."""

from __future__ import annotations

from typing import TYPE_CHECKING, Annotated, Literal

import pytest
from pydantic import BaseModel, Field

from celspresso import Env, NoRowMatches, Row, RuleCheck, Spec

if TYPE_CHECKING:
    from pathlib import Path


class Order(BaseModel):
    status: Literal["damaged", "lost", "late", "ok"]
    total: Annotated[int, Field(ge=0, le=100_000)]
    days: Annotated[int, Field(ge=0, le=365)]


class Decision(BaseModel):
    action: Literal["refund", "review", "deny"]
    amount: Annotated[int, Field(ge=0)]


ENV = Env(order=Order, structs=[Decision])
REFUND = "Decision{action: 'refund', amount: order.total}"
DENY = "Decision{action: 'deny', amount: 0}"
REVIEW = "Decision{action: 'review', amount: 0}"
SPEC = Spec(returns=Decision, ensures={"capped": "result.amount <= order.total"})


def kinds(r: RuleCheck) -> list[str]:
    return [p.kind for p in r.problems]


def test_a_complete_table_is_accepted_and_evaluates_first_match() -> None:
    t = ENV.decision_table(
        {
            "small lost": ("order.status == 'lost' && order.total <= 20000", REFUND),
            "big lost": ("order.status == 'lost'", REVIEW),
        },
        default=DENY,
    )
    assert t.check(SPEC).ok
    order = {"status": "lost", "total": 100, "days": 1}
    assert t.evaluate({"order": order}) == Decision(action="refund", amount=100)
    assert t.expr.evaluate({"order": order}) == Decision(action="refund", amount=100)
    assert t.matching_row({"order": {**order, "total": 50_000}}) == "big lost"
    assert t.evaluate({"order": {**order, "status": "ok"}}) == Decision(action="deny", amount=0)


def test_gaps_dead_rows_and_a_dead_default() -> None:
    t = ENV.decision_table(
        [
            Row("order.status == 'lost'", REVIEW, "lost"),
            Row("order.status == 'lost' && order.days < 5", DENY, "fresh lost"),
            Row("order.total < 0", DENY, "negative"),
            Row("order.status == 'damaged'", REFUND),
        ]
    )
    r = t.check(SPEC)
    assert kinds(r) == ["shadowed", "shadowed", "no_match"], str(r)
    assert "fresh lost never decides anything: lost catches every input it matches" in str(r)
    assert "negative never decides anything\n" in str(r) + "\n"  # its condition can't hold
    assert "no row matches when" in str(r)
    assert t.rows[3].name == "row 4"
    with pytest.raises(NoRowMatches):
        t.evaluate({"order": {"status": "ok", "total": 1, "days": 1}})

    full = ENV.decision_table([("order.total >= 0", DENY)], default=REVIEW)
    assert "the default is never used" in str(full.check(SPEC))


def test_the_whole_table_is_checked_as_a_rule_and_problems_name_the_row() -> None:
    t = ENV.decision_table(
        [("order.status == 'damaged'", "Decision{action: 'refund', amount: order.total + 1}")],
        default=DENY,
    )
    r = t.check(SPEC)
    assert kinds(r) == ["violates"]
    assert str(r).startswith("rejected:\n- row 1: violates ensures 'capped'")
    # with no default, inputs no row matches are a gap, not also an evaluation failure
    t = ENV.decision_table([("order.total >= 0", REFUND)])
    assert t.check(SPEC).ok


def test_unique_tables_reject_overlaps() -> None:
    rows = {"lost": ("order.status == 'lost'", REVIEW), "cheap": ("order.total < 10", DENY)}
    assert ENV.decision_table(rows, default=DENY).check(SPEC).ok
    r = ENV.decision_table(rows, default=DENY, unique=True).check(SPEC)
    assert kinds(r) == ["overlap"]
    assert "lost and cheap both match when" in str(r)


def test_bad_tables() -> None:
    with pytest.raises(ValueError, match="at least one row"):
        ENV.decision_table([])
    with pytest.raises(ValueError, match="distinct"):
        ENV.decision_table([Row("true", DENY, "a"), Row("false", DENY, "a")])
    with pytest.raises(TypeError, match="pair"):
        ENV.decision_table([("true",)])  # type: ignore[list-item]
    r = ENV.decision_table([("order.nope", DENY)]).check()
    assert kinds(r) == ["invalid"]
    r = ENV.decision_table([("true", DENY)], default="'deny'").check()
    assert kinds(r) == ["invalid"]
    # a comment in a row can't swallow the rest of the table
    t = ENV.decision_table([("order.total > 5 // big", REVIEW)], default=DENY)
    assert t.evaluate({"order": {"status": "ok", "total": 1, "days": 1}}) == Decision(action="deny", amount=0)
    assert t.check(SPEC).ok


TABLE_FILE = """
vars = {{ order = "{mod}:Order" }}
structs = ["{mod}:Decision"]
returns = "{mod}:Decision"

[rules]
plain = "{deny}"

[rules.refund]
default = "{deny}"
rows = [
  {{ name = "small lost", when = "order.status == 'lost' && order.total <= 20000", then = "{refund}" }},
  {{ name = "dead", when = "order.status == 'lost' && order.total < 5", then = "{refund}" }},
]

[ensures]
capped = "result.amount <= order.total"
"""


def test_rule_files_take_tables(tmp_path: Path, capsys: pytest.CaptureFixture[str]) -> None:
    from celspresso._cli import main

    mod = "tables_models"
    (tmp_path / f"{mod}.py").write_text(_models_source())
    f = tmp_path / "rules.toml"
    f.write_text(TABLE_FILE.format(mod=mod, deny=DENY, refund=REFUND))
    code = main(["check", str(f)])
    out = capsys.readouterr().out
    assert code == 1
    assert "plain: ok" in out
    assert "dead never decides anything: small lost catches every input it matches" in out
    # a table is diffed by what it does
    g = tmp_path / "new.toml"
    g.write_text(TABLE_FILE.format(mod=mod, deny=DENY, refund=REFUND).replace("<= 20000", "<= 30000"))
    main(["diff", str(f), str(g)])
    out = capsys.readouterr().out
    assert "refund: changed" in out
    assert "plain" not in out  # unchanged
    bad = tmp_path / "bad.toml"
    bad.write_text(TABLE_FILE.format(mod=mod, deny=DENY, refund=REFUND).replace("then =", "than ="))
    assert main(["check", str(bad)]) == 2
    assert "must have when and then" in capsys.readouterr().err
    # a table's line is its [rules.name] header
    main(["check", str(f), "--format", "json"])
    import json

    lines = TABLE_FILE.splitlines()
    assert json.loads(capsys.readouterr().out)["rules"]["refund"]["line"] == lines.index("[rules.refund]") + 1


def _models_source() -> str:
    return """
from typing import Annotated, Literal
from pydantic import BaseModel, Field

class Order(BaseModel):
    status: Literal["damaged", "lost", "late", "ok"]
    total: Annotated[int, Field(ge=0, le=100_000)]
    days: Annotated[int, Field(ge=0, le=365)]

class Decision(BaseModel):
    action: Literal["refund", "review", "deny"]
    amount: Annotated[int, Field(ge=0)]
"""


def test_a_condition_that_fails_is_not_coverage() -> None:
    env = Env(xs=Annotated[list[int], Field(max_length=3)])
    t = env.decision_table([("xs[0] > 0", "1"), ("xs[0] <= 0", "2")])
    r = t.check(Spec(ensures={"p": "result > 0"}))
    assert kinds(r) == ["no_match"], str(r)
    assert "a row's condition fails before any row matches when xs = []" in str(r)


def test_errors_name_the_row_and_evaluate_agrees_with_expr() -> None:
    from celspresso import CelError, TableRowError

    bad = ENV.decision_table([("true", DENY), ("order.total <", DENY)])
    with pytest.raises(TableRowError, match="row 2's condition"):
        bad.expr
    with pytest.raises(CelError):
        bad.evaluate({"order": {"status": "ok", "total": 1, "days": 1}})
    with pytest.raises(TypeError, match="CEL strings"):
        Row(123, "1")  # type: ignore[arg-type]
    r = ENV.decision_table({"a": ("true", DENY), "b": ("order.nope", DENY)}).check()
    assert str(r) == "rejected:\n- b's condition: " + str(r).split("b's condition: ")[1]
    assert "the default:" in str(ENV.decision_table([("true", DENY)], default="zz").check())
    mixed = ENV.decision_table([("order.total > 5", "1")], default="'a'")
    assert kinds(mixed.check()) == ["invalid"]
    with pytest.raises(CelError):
        mixed.evaluate({"order": {"status": "ok", "total": 1, "days": 1}})
