"""The `celspresso` command: rule files, check, diff, and every output format."""

from __future__ import annotations

import json
import re
import subprocess
import sys
import textwrap
from pathlib import Path

import pytest

from celspresso import Env
from celspresso._cli import RuleFile, _code, main

MODELS = """
from typing import Annotated, Literal
from pydantic import BaseModel, Field
from celspresso import Env, function

class Order(BaseModel):
    status: Literal["delivered", "damaged", "lost"]
    days: Annotated[int, Field(ge=0, le=365)]
    cents: Annotated[int, Field(ge=0, le=1_000_000)]

@function
def flagged(cents: int) -> bool:
    return True  # the solver can't know this, so its counterexamples won't replay

class Item(BaseModel):
    name: str
    tags: dict[str, int]

env = Env(order=Order).extend(functions=[flagged])
not_an_env = 3
"""

OLD = """
vars = { order = "{mod}:Order" }
assumptions = ["order.days <= 300"]

[rules]
damaged = "order.status == 'damaged' && order.days <= 30 && order.cents <= 50000"
lost = "order.status == 'lost' && order.cents <= 20000"
gone = "order.cents == 0"

[invariants]
capped = "order.cents <= 50000"

[require]
small = "order.status == 'damaged' && order.days <= 7 && order.cents <= 1000"
"""

NEW = """
vars = { order = "{mod}:Order" }
assumptions = ["order.days <= 300"]

[rules]
damaged = "order.status == 'damaged' && order.days < 31 && order.cents <= 50000"
lost = "order.status in ['lost', 'damaged'] && order.cents <= 60000"
fresh = "order.days <= 2 && order.cents <= 100 / (order.days - 1)"

[invariants]
capped = "order.cents <= 50000"

[require]
small = "order.status == 'damaged' && order.days <= 7 && order.cents <= 1000"
"""


@pytest.fixture
def project(tmp_path: Path, request: pytest.FixtureRequest) -> tuple[Path, str]:
    # a fresh module name per test: imports are cached
    mod = "models_" + re.sub(r"\W", "_", request.node.name)
    (tmp_path / f"{mod}.py").write_text(MODELS)
    return tmp_path, mod


def write(path: Path, text: str, mod: str) -> str:
    path.write_text(textwrap.dedent(text).replace("{mod}", mod))
    return str(path)


def run(capsys: pytest.CaptureFixture[str], *argv: str) -> tuple[int, str, str]:
    code = main(list(argv))
    out, err = capsys.readouterr()
    return code, out, err


def test_check_reports_each_rule(project: tuple[Path, str], capsys: pytest.CaptureFixture[str]):
    d, mod = project
    f = write(d / "rules.toml", NEW, mod)
    code, out, _ = run(capsys, "check", f)
    assert code == 1
    assert f"{f}:6: damaged: ok" in out
    assert f"{f}:7: lost: rejected" in out
    assert "violates 'capped' when order.cents = 50001, order.status = 'damaged'" in out
    assert "evaluation fails (division by zero) when order.cents = 0, order.days = 1" in out
    assert "too narrow: doesn't allow 'small'" in out
    assert out.rstrip().endswith("1 of 3 rules proved ok")

    code, out, _ = run(capsys, "check", f, "--rule", "damaged")
    assert (code, out.rstrip().splitlines()[-1]) == (0, "1 of 1 rules proved ok")


def test_check_formats(project: tuple[Path, str], capsys: pytest.CaptureFixture[str]):
    d, mod = project
    f = write(d / "rules.toml", NEW, mod)
    _, out, _ = run(capsys, "check", f, "--format", "json")
    data = json.loads(out)
    assert data["ok"] is False
    assert data["rules"]["damaged"] == {"ok": True, "line": 6, "problems": []}
    (violates,) = data["rules"]["lost"]["problems"]
    assert violates["kind"] == "violates"
    assert violates["condition"] == "capped"
    assert violates["example"] == {"order.cents": 50001, "order.status": "damaged"}

    _, out, _ = run(capsys, "check", f, "--format", "markdown")
    assert "**2 of 3 rules rejected.**" in out
    assert "- **may_error**: evaluation fails (division by zero)" in out

    _, out, _ = run(capsys, "check", f, "--format", "sarif")
    sarif = json.loads(out)
    assert sarif["version"] == "2.1.0"
    results = sarif["runs"][0]["results"]
    assert {r["ruleId"] for r in results} == {"violates", "may_error", "too_narrow"}
    lost = next(r for r in results if r["ruleId"] == "violates")
    assert lost["level"] == "error"
    assert lost["locations"][0]["physicalLocation"]["region"]["startLine"] == 7
    assert lost["message"]["text"].startswith("lost: violates 'capped'")


def test_check_all_ok_in_markdown(project: tuple[Path, str], capsys: pytest.CaptureFixture[str]):
    d, mod = project
    f = write(d / "rules.json", "", mod)
    (d / "rules.json").write_text(
        json.dumps({"vars": {"order": f"{mod}:Order", "n": "int"}, "rules": {"small": "n < 3 || n >= 3"}})
    )
    code, out, _ = run(capsys, "check", f, "--format", "markdown")
    assert (code, out.strip().splitlines()[-1]) == (0, "All 1 rules proved ok.")


def test_diff_two_files(project: tuple[Path, str], capsys: pytest.CaptureFixture[str]):
    d, mod = project
    old, new = write(d / "old.toml", OLD, mod), write(d / "new.toml", NEW, mod)
    code, out, _ = run(capsys, "diff", old, new, "--no-check")
    assert code == 0
    assert "damaged: unchanged (rewritten, but proved equivalent)" in out
    assert "lost: changed\n  when order.cents = 0, order.status = 'damaged': false -> true" in out
    assert "gone: removed" in out
    assert "fresh: added" in out
    assert run(capsys, "diff", old, new, "--no-check", "--fail-on-change")[0] == 1
    assert run(capsys, "diff", old, old, "--fail-on-change")[:2] == (0, "no rule changed behaviour\n")

    # by default, added and changed rules are also checked against the invariants
    code, out, _ = run(capsys, "diff", old, new)
    assert code == 1
    assert "checks on added and changed rules:" in out
    assert "damaged: ok" not in out.split("checks on")[1]  # unchanged rules aren't rechecked


def test_diff_formats(project: tuple[Path, str], capsys: pytest.CaptureFixture[str]):
    d, mod = project
    old, new = write(d / "old.toml", OLD, mod), write(d / "new.toml", NEW, mod)
    _, out, _ = run(capsys, "diff", old, new, "--format", "markdown", "--limit", "2")
    assert "**1 changed**, **1 added**, **1 removed**, 1 unchanged" in out
    assert "- order.status == 'lost' && order.cents <= 20000\n+ order.status in" in out
    assert "| `order.cents = 0, order.status = 'damaged'` | false | **true** |" in out
    assert "### celspresso check:" in out

    _, out, _ = run(capsys, "diff", old, new, "--format", "json")
    data = json.loads(out)
    by_rule = {c["name"]: c for c in data["changes"] if c["section"] == "rules"}
    assert by_rule["lost"]["examples"][0] == {
        "input": {"order.cents": 0, "order.status": "damaged"},
        "old": "false",
        "new": "true",
    }
    assert by_rule["gone"]["status"] == "removed"
    assert data["check"]["ok"] is False

    _, out, _ = run(capsys, "diff", old, new, "--format", "sarif", "--no-check")
    results = json.loads(out)["runs"][0]["results"]
    assert {(r["ruleId"], r["level"]) for r in results} == {
        ("behaviour_changed", "note"),
        ("rule_added", "note"),
        ("rule_removed", "note"),
    }

    _, out, _ = run(capsys, "diff", old, old, "--format", "markdown")
    assert "No rule changed behaviour (3 rules compared)." in out


def test_diff_undecided_and_invalid(project: tuple[Path, str], capsys: pytest.CaptureFixture[str]):
    d, mod = project
    old = d / "old.json"
    new = d / "new.json"
    old.write_text(json.dumps({"env": f"{mod}:env", "rules": {"f": "flagged(order.cents)", "bad": "true"}}))
    new.write_text(
        json.dumps(
            {"env": f"{mod}:env", "rules": {"f": "flagged(order.cents) || order.days > 100", "bad": "nope"}}
        )
    )
    code, out, _ = run(capsys, "diff", str(old), str(new), "--no-check")
    assert code == 1  # an invalid rule fails the diff
    assert "f: undecided\n  the answer depends on what 'flagged' returns" in out
    assert "bad: invalid\n  the new version doesn't compile: " in out
    # an undecided rule alone fails the diff too
    new.write_text(
        json.dumps({"env": f"{mod}:env", "rules": {"f": "flagged(order.cents) || order.days > 100"}})
    )
    assert run(capsys, "diff", str(old), str(new), "--no-check")[0] == 1
    new.write_text(
        json.dumps(
            {"env": f"{mod}:env", "rules": {"f": "flagged(order.cents) || order.days > 100", "bad": "nope"}}
        )
    )
    _, out, _ = run(capsys, "diff", str(old), str(new), "--no-check", "--format", "markdown")
    assert "#### `f`: undecided" in out
    assert "> the answer depends on what 'flagged' returns" in out
    _, out, _ = run(capsys, "diff", str(old), str(new), "--no-check", "--format", "sarif")
    levels = {r["ruleId"]: r["level"] for r in json.loads(out)["runs"][0]["results"]}
    assert levels == {"undecided": "warning", "invalid": "error"}


def git(d: Path, *args: str) -> None:
    subprocess.run(
        ["git", "-c", "user.email=t@t", "-c", "user.name=t", *args], cwd=d, check=True, capture_output=True
    )


def test_diff_against_a_git_revision(project: tuple[Path, str], capsys: pytest.CaptureFixture[str]):
    d, mod = project
    f = write(d / "rules.toml", OLD, mod)
    git(d, "init", "-q")
    git(d, "add", ".")
    git(d, "commit", "-qm", "base")
    write(d / "rules.toml", NEW, mod)
    code, out, _ = run(capsys, "diff", f, "--against", "HEAD", "--no-check", "--format", "markdown")
    assert code == 0
    assert "(HEAD → working tree)" in out
    assert "#### `lost`: changed" in out

    # a file that is new since the revision: every rule is added
    g = write(d / "more.toml", NEW, mod)
    _, out, _ = run(capsys, "diff", g, "--against", "HEAD", "--no-check")
    assert out.splitlines() == [
        "damaged: added",
        "lost: added",
        "fresh: added",
        "invariant capped: added",
        "  + order.cents <= 50000",
        "require small: added",
        "  + order.status == 'damaged' && order.days <= 7 && order.cents <= 1000",
        "assumption: added",
        "  + order.days <= 300",
    ]

    code, _, err = run(capsys, "diff", f, "--against", "no-such-ref")
    assert code == 2
    assert "git show no-such-ref:rules.toml failed" in err


@pytest.mark.parametrize(
    ("name", "text", "error"),
    [
        ("r.txt", "x", "unknown rule file type '.txt'"),
        ("r.json", "{", "not valid JSON"),
        ("r.json", "[1]", "expected a table of settings"),
        ("r.yaml", "rules: {}", "reading YAML needs PyYAML"),
        ("r.toml", 'env = "{mod}:env"\nvars = {}', "give either env or vars, not both"),
        ("r.toml", 'env = "{mod}:not_an_env"', "is a int, not a celspresso Env"),
        ("r.toml", 'env = "{mod}:missing"', "has no attribute 'missing'"),
        ("r.toml", 'env = "no_such_module_xyz:env"', "can't import 'no_such_module_xyz'"),
        ("r.toml", 'vars = { x = "list" }', "expected 'module:attribute'"),
        ("r.toml", "rules = {}", "declare the rules' variables"),
        ("r.toml", 'vars = { x = "{mod}:flagged" }', "r.toml: "),
        ("r.toml", 'vars = { x = "int" }\nrule = {}', "unknown setting(s): rule"),
        ("r.toml", 'vars = { x = "int" }\nassumptions = "x > 1"', "assumptions must be a list"),
        ("r.toml", 'vars = { x = "int" }\nrules = { a = 1 }', "[rules] must map names to CEL expressions"),
        ("r.toml", 'vars = { x = "int" }', "r.toml: no rules to check"),
        ("r.toml", 'vars = { x = "int" }\n[rules]', "r.toml: no rules to check"),
        (
            "r.toml",
            'vars = { x = "int" }\nrules = { a = "x > 1" }\n[invariants]\ni = "x.nope"',
            "r.toml: [invariants] i doesn't compile: ",
        ),
        (
            "r.toml",
            'vars = { x = "int" }\nrules = { a = "x > 1" }\n[require]\nq = "x"',
            "[require] q doesn't",
        ),
        (
            "r.toml",
            'vars = { x = "int" }\nassumptions = ["y > 1"]\nrules = { a = "x"}',
            "assumptions[0] doesn't",
        ),
    ],
)
def test_unusable_rule_files(
    project: tuple[Path, str], capsys: pytest.CaptureFixture[str], name: str, text: str, error: str
):
    d, mod = project
    f = write(d / name, text, mod)
    code, out, err = run(capsys, "check", f)
    assert (code, out) == (2, "")
    assert err.startswith("celspresso: ")
    assert error in err


def test_usage_errors(project: tuple[Path, str], capsys: pytest.CaptureFixture[str]):
    d, mod = project
    f = write(d / "rules.toml", OLD, mod)
    assert "can't read" in run(capsys, "check", str(d / "missing.toml"))[2]
    assert "no rule named 'nope'" in run(capsys, "check", f, "--rule", "nope")[2]
    assert "diff needs two files" in run(capsys, "diff", f)[2]
    assert "either two files, or one file and --against" in run(capsys, "diff", f, f, "--against", "HEAD")[2]
    assert "from git" in run(capsys, "diff", f, "--against", "HEAD")[2]  # not a git repository


def test_python_dash_m_and_example():
    out = subprocess.run(
        [sys.executable, "-m", "celspresso", "check", "examples/refunds/rules.toml"],
        capture_output=True,
        text=True,
        check=False,
    )
    assert out.returncode == 0, out.stderr
    assert "2 of 2 rules proved ok" in out.stdout


def test_unusable_new_file_in_diff(project: tuple[Path, str], capsys: pytest.CaptureFixture[str]):
    d, mod = project
    old = write(d / "old.toml", OLD, mod)
    empty = write(d / "empty.toml", 'vars = { x = "int" }', mod)
    code, out, err = run(capsys, "diff", old, empty)
    assert (code, out) == (2, "")
    assert "empty.toml: no rules to check" in err
    bad = write(d / "bad.toml", NEW + 'cap = "order.nope"\n', mod)  # the last table is [require]
    code, _, err = run(capsys, "diff", old, bad, "--no-check")
    assert code == 2
    assert "bad.toml: [require] cap doesn't compile" in err


def test_internal_errors_are_not_rejections(
    project: tuple[Path, str], capsys: pytest.CaptureFixture[str], monkeypatch: pytest.MonkeyPatch
):
    d, mod = project
    f = write(d / "rules.toml", OLD, mod)

    def boom(*args: object, **kwargs: object) -> None:
        raise RuntimeError("solver exploded")

    monkeypatch.setattr("celspresso._cli.run_check", boom)
    code, out, err = run(capsys, "check", f)
    assert (code, out) == (2, "")
    assert err == "celspresso: internal error: RuntimeError: solver exploded\n"


CAPPED_OLD = """
vars = { order = "{mod}:Order" }
assumptions = ["order.days <= 300"]

[rules]
lost = "order.status == 'lost' && order.cents <= 20000"
other = "order.status == 'delivered' && order.cents <= 20000"

[invariants]
capped = "order.cents <= 50000"

[require]
small = "order.status == 'lost' && order.cents <= 100"
"""

CAPPED_NEW = """
vars = { order = "{mod}:Order" }
assumptions = ["order.days <= 200"]

[rules]
lost = "order.status == 'lost' && order.cents <= 20000"
other = "order.status == 'delivered' && order.cents <= 20000"

[invariants]
capped = "order.cents <= 10000"
recent = "order.days <= 365"
"""


def test_diff_reports_edits_to_the_checks(project: tuple[Path, str], capsys: pytest.CaptureFixture[str]):
    d, mod = project
    old, new = write(d / "old.toml", CAPPED_OLD, mod), write(d / "new.toml", CAPPED_NEW, mod)
    code, out, _ = run(capsys, "diff", old, new)
    assert code == 1  # the tightened invariant now rejects both (unchanged) rules
    assert out.split("\n\n")[0].splitlines() == [
        "invariant capped: changed",
        "  - order.cents <= 50000",
        "  + order.cents <= 10000",
        "invariant recent: added",
        "  + order.days <= 365",
        "require small: removed",
        "  - order.status == 'lost' && order.cents <= 100",
        "assumption: removed",
        "  - order.days <= 300",
        "assumption: added",
        "  + order.days <= 200",
    ]
    assert "checks on every rule (invariants, require entries or assumptions changed):" in out
    assert f"{new}:6: lost: rejected" in out
    assert f"{new}:7: other: rejected" in out
    assert run(capsys, "diff", old, new, "--no-check")[0] == 0
    assert run(capsys, "diff", old, new, "--no-check", "--fail-on-change")[0] == 1

    _, out, _ = run(capsys, "diff", old, new, "--format", "json", "--no-check")
    edits = {(c["section"], c["name"], c["status"]) for c in json.loads(out)["changes"]}
    assert edits >= {
        ("invariants", "capped", "changed"),
        ("invariants", "recent", "added"),
        ("require", "small", "removed"),
        ("assumptions", "order.days <= 300", "removed"),
        ("assumptions", "order.days <= 200", "added"),
    }

    _, out, _ = run(capsys, "diff", old, new, "--format", "markdown", "--no-check")
    assert "2 unchanged, **5 invariant, require or assumption edits**" in out
    assert (
        "#### invariant `capped`: changed\n\n```diff\n- order.cents <= 50000\n+ order.cents <= 10000" in out
    )
    assert "#### assumption: added\n\n```cel\norder.days <= 200\n```" in out

    _, out, _ = run(capsys, "diff", old, new, "--format", "sarif", "--no-check")
    lines = {
        r["ruleId"]: r["locations"][0]["physicalLocation"]["region"]["startLine"]
        for r in json.loads(out)["runs"][0]["results"]
    }
    # removed entries point at their section (or the assumptions) in the new file
    assert lines == {
        "invariant_changed": 10,
        "invariant_added": 11,
        "require_removed": 1,
        "assumption_removed": 3,
        "assumption_added": 3,
    }


def test_diff_compares_under_shared_assumptions(
    project: tuple[Path, str], capsys: pytest.CaptureFixture[str]
):
    d, mod = project
    # a new assumption can't hide that the cap was dropped
    old = write(
        d / "old.toml", 'vars = { order = "{mod}:Order" }\nrules = { lost = "order.cents <= 200" }', mod
    )
    new = write(
        d / "new.toml",
        'vars = { order = "{mod}:Order" }\nassumptions = ["order.cents <= 100"]\nrules = { lost = "true" }',
        mod,
    )
    _, out, _ = run(capsys, "diff", old, new, "--no-check")
    assert "lost: changed\n  when order.cents = 201: false -> true" in out
    # and examples satisfy the assumptions both files share
    shared = 'vars = { order = "{mod}:Order" }\nassumptions = ["order.cents == 777"]\n'
    old = write(d / "old.toml", shared + "rules = { r = \"order.status == 'lost'\" }", mod)
    new = write(d / "new.toml", shared + "rules = { r = \"order.status == 'lost' || order.cents > 5\" }", mod)
    _, out, _ = run(capsys, "diff", old, new, "--no-check")
    assert out.startswith("r: changed\n  when order.cents = 777, order.status = ")


def test_diff_with_rules_that_dont_compile(project: tuple[Path, str], capsys: pytest.CaptureFixture[str]):
    d, mod = project
    head = 'vars = { order = "{mod}:Order" }\n[rules]\n'
    broken = write(d / "broken.toml", head + "r = \"order.state == 'lost'\"\n", mod)
    fixed = write(d / "fixed.toml", head + "r = \"order.status == 'lost'\"\n", mod)
    more = write(d / "more.toml", head + 'r = "order.status == \'lost\'"\nx = "order.zzz"\n', mod)
    code, out, _ = run(capsys, "diff", broken, fixed)
    assert code == 0
    assert out.startswith("r: added\n  the old version didn't compile: ")
    assert "checks on added and changed rules:" in out
    _, out, _ = run(capsys, "diff", broken, fixed, "--format", "sarif")
    (added,) = json.loads(out)["runs"][0]["results"]
    assert added["message"]["text"].startswith("r: rule added (the old version didn't compile: ")

    # a new rule that doesn't compile always fails, even when it's added or unchecked
    code, out, _ = run(capsys, "diff", fixed, more, "--no-check")
    assert code == 1
    assert out.startswith("x: invalid\n  the new version doesn't compile: ")
    code, out, _ = run(capsys, "diff", broken, broken, "--no-check")
    assert (code, out.splitlines()[0]) == (1, "r: invalid")
    assert run(capsys, "diff", more, fixed, "--no-check")[:2] == (0, "x: removed\n")


ESCAPES_OLD = """
vars = { m = "{mod}:Item" }
[rules]
r = \"\"\"m.name == 'a`|b' ||
  m.name == 'z'\"\"\"
k = "m.tags['x|y'] > 0"
"""

ESCAPES_NEW = """
vars = { m = "{mod}:Item" }
[rules]
r = \"\"\"m.name == 'a`|b' ||
  m.name == 'q'\"\"\"
k = "'x|y' in m.tags && m.tags['x|y'] > 0"
w = "m.name == '`x``'"
"""


def test_diff_markdown_escaping(project: tuple[Path, str], capsys: pytest.CaptureFixture[str]):
    d, mod = project
    old = write(d / "old.toml", ESCAPES_OLD + 'w = "false"\n', mod)
    new = write(d / "new.toml", ESCAPES_NEW, mod)
    _, out, _ = run(capsys, "diff", old, new, "--no-check", "--format", "markdown", "--limit", "1")
    # only the line that changed is marked
    assert "```diff\n  m.name == 'a`|b' ||\n-   m.name == 'z'\n+   m.name == 'q'\n```" in out
    # every cell is escaped, before and after values included
    assert re.search(r'\| `m\.tags = \{.*\}` \| error \(no such key: "x\\\|y"\) \| \*\*false\*\* \|', out)
    # backticks in a witness are kept, inside a longer fence
    assert "| ```m.name = '`x``'``` | false | **true** |" in out
    assert (_code("`a"), _code("a b")) == ("`` `a ``", "`a b`")  # padded only when needed


def test_sarif_uri_is_relative_to_the_repository(
    project: tuple[Path, str], capsys: pytest.CaptureFixture[str]
):
    d, mod = project
    (d / "policy").mkdir()
    (d / "policy" / f"{mod}.py").write_text(MODELS)
    f = write(d / "policy" / "rules.toml", NEW, mod)
    _, out, _ = run(capsys, "check", f, "--format", "sarif")
    location = json.loads(out)["runs"][0]["results"][0]["locations"][0]["physicalLocation"]
    assert location["artifactLocation"] == {"uri": Path(f).as_posix()}  # not in git: as given
    git(d, "init", "-q")
    _, out, _ = run(capsys, "check", f, "--format", "sarif")
    location = json.loads(out)["runs"][0]["results"][0]["locations"][0]["physicalLocation"]
    assert location["artifactLocation"] == {"uri": "policy/rules.toml", "uriBaseId": "%SRCROOT%"}


def test_lines_come_from_the_right_section(project: tuple[Path, str], capsys: pytest.CaptureFixture[str]):
    d, mod = project
    text = """
    vars = { order = "{mod}:Order" }
    rules = { capped = "order.cents <= 60000", "ok" = "order.cents < 5" }

    [invariants]
    capped = "order.cents <= 50000"
    """
    f = write(d / "rules.toml", text, mod)
    _, out, _ = run(capsys, "check", f, "--format", "json")
    assert json.loads(out)["rules"]["capped"]["line"] == 3
    _, out, _ = run(capsys, "check", f)
    assert out.splitlines()[0] == f"{f}:3: capped: rejected"
    _, out, _ = run(capsys, "check", f, "--format", "sarif")
    (result,) = json.loads(out)["runs"][0]["results"]
    assert result["locations"][0]["physicalLocation"]["region"]["startLine"] == 3


def test_line_of_in_each_format():
    env = Env(x=int)
    toml = 'vars = { x = "int" }\nrules.a = "x > 1"\n[invariants]\na = "x < 9"\n[require]\n"a" = "x == 5"\n'
    rf = RuleFile("r.toml", toml, env, {})
    assert [rf.line_of("a", s) for s in ("rules", "invariants", "require")] == [2, 4, 6]
    assert (rf.line_of("zz", "require"), rf.line_of("zz", "rules"), rf.line_of("x", "assumptions")) == (
        5,
        1,
        1,
    )
    yaml = (
        "vars:\n  x: int\nrules:\n  a: x > 1\n  # note\n  b: x > 2\n"
        "invariants: {a: x < 9}\nrequire:\n  a: x\n"
    )
    rf = RuleFile("r.yaml", yaml, env, {})
    assert [rf.line_of(n, s) for n, s in [("a", "rules"), ("b", "rules"), ("a", "invariants")]] == [4, 6, 7]
    assert [rf.line_of(n, s) for n, s in [("a", "require"), ("zz", "require"), ("zz", "rules")]] == [9, 8, 3]
    js = (
        '{"vars": {"x": "int"},\n "rules": {\n  "a": "x > 1 \\" a: {",\n  "b": "x"},\n'
        ' "invariants": {"a": "x"}\n}'
    )
    rf = RuleFile("r.json", js, env, {})
    assert [rf.line_of(n, s) for n, s in [("a", "rules"), ("b", "rules"), ("a", "invariants")]] == [3, 4, 5]
    assert (rf.line_of("a", "require"), rf.line_of("zz", "rules")) == (1, 2)
