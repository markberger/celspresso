"""`celspresso check` and `celspresso diff`: verify rule files from the command line or CI.

A rule file (TOML, JSON, or YAML when PyYAML is installed) names its variables and rules::

    vars = { order = "refunds:Order" }      # "module:attribute"; or env = "policy:env"
    assumptions = ["order.total_cents < 1000000"]

    [rules]
    auto_refund = "order.status == 'damaged' && order.days_since_delivery <= 30"

    [invariants]                             # what no rule may ever allow
    capped = "order.total_cents <= 50000"

    [require]                                # what each rule must allow
    damaged_recent = "order.status == 'damaged' && order.days_since_delivery <= 7"

Rules may compute a value instead (an amount, a label, a struct). Say what every result
must satisfy with `ensures`, over the inputs and `result`::

    vars = { order = "refunds:Order" }
    structs = ["refunds:Decision"]           # classes the rules may build: Decision{...}
    returns = "refunds:Decision"             # optional: the type every rule must give
    # (a file's rules share its spec: give true/false and value rules separate files)

    [rules]
    refund = '''order.status == 'lost'
        ? Decision{action: 'refund', amount: order.total_cents}
        : Decision{action: 'deny', amount: 0}'''

    [ensures]
    capped = "result.amount <= order.total_cents"

Invariants and require entries apply only to true/false rules.

Exit status:

- 0: everything was proved.
- 1: a rule has problems. For `check`, a rule was rejected. For `diff`, a rule in the new
  file is invalid or undecided, or fails its check; with `--fail-on-change`, also any
  change to a rule's behaviour, the spec (invariants, require, ensures, returns) or an
  assumption.
- 2: the command line or the file can't be used (including a file with no rules), or
  celspresso itself failed.
"""

from __future__ import annotations

import argparse
import difflib
import importlib
import json
import re
import subprocess
import sys
from dataclasses import dataclass, field
from pathlib import Path
from typing import TYPE_CHECKING, Any

from . import __version__
from ._env import Env, Expr, Problem, RuleCheck, _value_or_error
from ._errors import CelError
from ._spec import Spec
from ._verdict import Difference, _outcome

if TYPE_CHECKING:
    from collections.abc import Callable, Sequence

    from ._verdict import Witness

__all__ = ["main"]

_TYPES: dict[str, Any] = {"int": int, "str": str, "bool": bool}
_SECTIONS = ("rules", "invariants", "require", "ensures")
_CONDITIONS = ("invariants", "require", "ensures")
_SINGULAR = {
    "rules": "rule",
    "invariants": "invariant",
    "require": "require",
    "ensures": "ensures",
    "returns": "returns",
    "assumptions": "assumption",
}


class UsageError(Exception):
    """The command line or the rule file can't be used (exit status 2)."""


# -- rule files -------------------------------------------------------------


@dataclass
class RuleFile:
    path: str
    text: str
    env: Env
    rules: dict[str, str]
    invariants: dict[str, str] = field(default_factory=dict)
    require: dict[str, str] = field(default_factory=dict)
    ensures: dict[str, str] = field(default_factory=dict)
    assumptions: list[str] = field(default_factory=list)
    returns: str | None = None  # as written in the file
    returns_type: Any = None

    @property
    def spec(self) -> Spec:
        """The file's invariants, require and ensures entries, result type and
        assumptions, as one Spec."""
        return Spec(
            self.invariants,
            require=self.require,
            ensures=self.ensures,
            returns=self.returns_type,
            assumptions=self.assumptions,
        )

    def line_of(self, name: str, section: str = "rules") -> int:
        """The 1-based line that defines `name` in `section` ("rules", "invariants",
        "require", or "assumptions" with the assumption's text as `name`). Falls back to
        the section's own line, then to 1. Best effort for YAML and JSON."""
        if section == "assumptions":
            return _assumption_line(self.text.splitlines(), name)
        suffix = Path(self.path).suffix.lower()
        if suffix == ".json":
            found = _json_line(self.text, section, name)
        elif suffix in (".yaml", ".yml"):
            found = _yaml_line(self.text.splitlines(), section, name)
        else:
            found = _toml_line(self.text.splitlines(), section, name)
        return found or 1


def _key(word: str, group: int) -> str:
    """A regex for `word` as a key, bare or quoted; `group` is the number of its quote group."""
    return rf"""(["']?){re.escape(word)}\{group}"""


def _toml_line(lines: list[str], section: str, name: str) -> int:
    key = re.compile(rf"^\s*{_key(name, 1)}\s*=")
    dotted = re.compile(rf"^\s*{_key(section, 1)}\s*\.\s*{_key(name, 2)}\s*=")
    inline = re.compile(rf"^\s*{_key(section, 1)}\s*=\s*\{{")
    inline_key = re.compile(rf"[{{,]\s*{_key(name, 1)}\s*=")
    header = re.compile(r"^\s*\[([^\[\]]+)\]")
    current, head = "", 0
    for i, line in enumerate(lines, 1):
        m = header.match(line)
        if m:
            current = m.group(1).strip().strip("\"'")
            head = i if current == section and not head else head
        elif current == section:
            if key.match(line):
                return i
        elif not current and inline.match(line):
            if inline_key.search(line):
                return i
            head = head or i
        elif not current and dotted.match(line):
            return i
    return head


def _yaml_line(lines: list[str], section: str, name: str) -> int:
    top = re.compile(rf"^{_key(section, 1)}\s*:(.*)$")
    key = re.compile(rf"^\s+{_key(name, 1)}\s*:")
    flow = re.compile(rf"[{{,]\s*{_key(name, 1)}\s*:")
    head = 0
    for i, line in enumerate(lines, 1):
        if not head:
            m = top.match(line)
            if m:
                head = i
                if flow.search(m.group(2)):
                    return i
        elif line.strip() and not line[0].isspace() and not line.startswith("#"):
            break  # the next top-level key
        elif key.match(line):
            return i
    return head


_COLON = re.compile(r"\s*:")


def _json_line(text: str, section: str, name: str) -> int:
    """Scan the (already parsed, so valid) JSON for `name` inside the top-level `section`."""
    stack: list[str | None] = []
    pending: str | None = None
    line, i, head = 1, 0, 0
    while i < len(text):
        c = text[i]
        if c == "\n":
            line += 1
        elif c == '"':
            j = i + 1
            while text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            if _COLON.match(text, j + 1):
                pending = json.loads(text[i : j + 1])
                if stack == [None] and pending == section:
                    head = line
                elif stack == [None, section] and pending == name:
                    return line
            i = j
        elif c in "{[":
            stack.append(pending)
            pending = None
        elif c in "}]":
            stack.pop()
        i += 1
    return head


def _assumption_line(lines: list[str], text: str) -> int:
    """The line holding `text` at or after the `assumptions` key; that key's line; or 1."""
    start = next(
        (i for i, line in enumerate(lines) if re.search(rf"{_key('assumptions', 1)}\s*[=:]", line)), None
    )
    if start is None:
        return 1
    return next((i + 1 for i in range(start, len(lines)) if text in lines[i]), start + 1)


def parse(text: str, path: str) -> dict[str, Any]:
    """The rule file's contents as plain data; the format is chosen by extension."""
    suffix = Path(path).suffix.lower()
    try:
        if suffix == ".json":
            data = json.loads(text)
        elif suffix in (".yaml", ".yml"):
            try:
                import yaml  # type: ignore[import-untyped]
            except ImportError:
                raise UsageError(f"{path}: reading YAML needs PyYAML (pip install pyyaml)") from None
            data = yaml.safe_load(text)
        elif suffix == ".toml":
            data = _toml().loads(text)
        else:
            raise UsageError(f"{path}: unknown rule file type {suffix!r} (use .toml, .json or .yaml)")
    except UsageError:
        raise
    except Exception as e:  # noqa: BLE001 - each parser has its own error type
        raise UsageError(f"{path}: not valid {suffix[1:].upper()}: {e}") from None
    if not isinstance(data, dict):
        raise UsageError(f"{path}: expected a table of settings at the top level")
    return data


def _toml() -> Any:
    try:
        import tomllib

        return tomllib
    except ImportError:  # pragma: no cover - Python 3.10
        try:
            import tomli  # type: ignore[import-not-found]

            return tomli
        except ImportError:
            raise UsageError("reading TOML on Python 3.10 needs tomli (pip install tomli)") from None


def _import(ref: str, what: str) -> Any:
    """`module:attr.path`, or a builtin type name."""
    if ref in _TYPES:
        return _TYPES[ref]
    module, sep, attr = ref.partition(":")
    if not sep or not module or not attr:
        raise UsageError(f"{what}: expected 'module:attribute' (or int, str, bool), got {ref!r}")
    try:
        obj: Any = importlib.import_module(module)
    except ImportError as e:
        raise UsageError(f"{what}: can't import {module!r}: {e}") from None
    try:
        for part in attr.split("."):
            obj = getattr(obj, part)
    except AttributeError:
        raise UsageError(f"{what}: {module!r} has no attribute {attr!r}") from None
    return obj


def _strings(data: dict[str, Any], key: str, path: str) -> dict[str, str]:
    raw = data.get(key, {})
    if not isinstance(raw, dict) or not all(isinstance(v, str) for v in raw.values()):
        raise UsageError(f"{path}: [{key}] must map names to CEL expressions (strings)")
    return {str(k): v for k, v in raw.items()}


def build_env(data: dict[str, Any], path: str) -> Env:
    """The Env a rule file describes: `env = "module:attr"`, or a table of `vars`; plus
    any `structs` the rules build."""
    _add_import_paths(path)
    if "env" in data and "vars" in data:
        raise UsageError(f"{path}: give either env or vars, not both")
    raw_structs = data.get("structs", [])
    if not isinstance(raw_structs, list) or not all(isinstance(t, str) for t in raw_structs):
        raise UsageError(f'{path}: structs must be a list of types ("module:Type")')
    structs = [_import(t, f"{path}: structs") for t in raw_structs]
    if "env" in data:
        env = _import(str(data["env"]), f"{path}: env")
        if not isinstance(env, Env):
            raise UsageError(f"{path}: env {data['env']!r} is a {type(env).__name__}, not a celspresso Env")
        if not structs:
            return env
        try:
            return env.extend(structs=structs)
        except (TypeError, ValueError) as e:
            raise UsageError(f"{path}: {e}") from None
    raw = data.get("vars")
    if not isinstance(raw, dict) or not raw:
        raise UsageError(f'{path}: declare the rules\' variables with vars = {{ name = "module:Type" }}')
    variables = {str(n): _import(str(t), f"{path}: vars.{n}") for n, t in raw.items()}
    try:
        return Env(variables, structs=structs)
    except (TypeError, ValueError) as e:
        raise UsageError(f"{path}: {e}") from None


def _add_import_paths(path: str) -> None:
    """Let `module:attr` references find modules next to the file and in the cwd."""
    sys.path[:0] = [p for p in (str(Path(path).resolve().parent), str(Path.cwd())) if p not in sys.path]


def load(path: str, *, text: str | None = None, env: Env | None = None, validate: bool = True) -> RuleFile:
    """Read a rule file. `text` overrides the file's contents (an older git revision),
    and `env` reuses an Env instead of building the file's own. With `validate`, every
    invariant, require entry and assumption must compile (rules, and ensures entries,
    which depend on a rule's result, are reported per rule)."""
    if text is None:
        try:
            text = Path(path).read_text(encoding="utf-8")
        except OSError as e:
            raise UsageError(f"can't read {path}: {e.strerror}") from None
    data = parse(text, path)
    unknown = set(data) - {"env", "vars", "structs", "returns", "assumptions", *_SECTIONS}
    if unknown:
        raise UsageError(f"{path}: unknown setting(s): {', '.join(sorted(unknown))}")
    assumptions = data.get("assumptions", [])
    if not isinstance(assumptions, list) or not all(isinstance(a, str) for a in assumptions):
        raise UsageError(f"{path}: assumptions must be a list of CEL expressions (strings)")
    returns = data.get("returns")
    if returns is not None and not isinstance(returns, str):
        raise UsageError(f'{path}: returns must be a type ("module:Type", or int, str, bool)')
    env = env if env is not None else build_env(data, path)
    if returns is not None:
        _add_import_paths(path)
    rf = RuleFile(
        path=path,
        text=text,
        env=env,
        rules=_strings(data, "rules", path),
        invariants=_strings(data, "invariants", path),
        require=_strings(data, "require", path),
        ensures=_strings(data, "ensures", path),
        assumptions=assumptions,
        returns=returns,
        returns_type=None if returns is None else _import(returns, f"{path}: returns"),
    )
    if rf.returns_type is not None:
        try:
            rf.env._builder.copy().convert(rf.returns_type, "returns")
        except (TypeError, ValueError) as e:
            raise UsageError(
                f"{path}: returns = {returns!r} is not a type celspresso can check: {e}"
            ) from None
    if validate:
        conditions = [
            *((f"[{s}] {k}", v) for s in ("invariants", "require") for k, v in getattr(rf, s).items()),
            *((f"assumptions[{i}]", a) for i, a in enumerate(assumptions)),
        ]
        for where, source in conditions:
            _validate(rf.env, source, f"{path}: {where}")
    return rf


def _validate(env: Env, source: str, where: str) -> None:
    try:
        env.predicate(source)
    except CelError as e:
        raise UsageError(f"{where} doesn't compile: {e}") from None


def _git_root(p: Path) -> str:
    """The top of the git repository holding the (resolved) file `p`; raises if there's none."""
    return subprocess.run(
        ["git", "rev-parse", "--show-toplevel"], cwd=p.parent, capture_output=True, text=True, check=True
    ).stdout.strip()


def git_show(ref: str, path: str) -> str | None:
    """`path` as of git revision `ref`, or None if it didn't exist there."""
    p = Path(path).resolve()
    try:
        root = _git_root(p)
        rel = p.relative_to(Path(root).resolve()).as_posix()
        out = subprocess.run(
            ["git", "show", f"{ref}:{rel}"], cwd=root, capture_output=True, text=True, check=False
        )
    except (OSError, subprocess.CalledProcessError, ValueError) as e:
        raise UsageError(f"can't read {path} from git: {e}") from None
    if out.returncode != 0:
        if "exists on disk, but not in" in out.stderr or "does not exist in" in out.stderr:
            return None
        raise UsageError(f"git show {ref}:{rel} failed: {out.stderr.strip()}")
    return out.stdout


# -- check ------------------------------------------------------------------


def run_check(
    rf: RuleFile, names: Sequence[str] | None = None, timeout: float | None = None
) -> dict[str, RuleCheck]:
    """`Env.check_rule` on each rule (or just `names`), with the file's invariants,
    requirements and assumptions."""
    return {
        n: rf.env.check_rule(rf.rules[n], rf.spec, timeout=timeout)
        for n in (rf.rules if names is None else names)
    }


# -- diff -------------------------------------------------------------------


@dataclass
class Example:
    """One input on which the old and new rule disagree."""

    witness: Witness
    old: str
    new: str


@dataclass
class Change:
    """One entry of a diff. For a rule (`section="rules"`): how its behaviour changed, one
    of added, removed, changed, unchanged, undecided or invalid. For an invariant, a
    require or ensures entry, the result type or an assumption: added, removed or
    changed (assumptions, a list, are named by their text and are only ever added or
    removed)."""

    name: str
    status: str
    old: str | None
    new: str | None
    examples: list[Example] = field(default_factory=list)
    reason: str | None = None
    section: str = "rules"

    @property
    def label(self) -> str:
        if self.section == "rules":
            return self.name
        if self.section in ("assumptions", "returns"):
            return _SINGULAR[self.section]  # one entry, named by its value
        return f"{_SINGULAR[self.section]} {self.name}"


def _compile(env: Env, source: str | None) -> tuple[Expr[Any] | None, str | None]:
    if source is None:
        return None, None
    try:
        return env.compile(source), None
    except CelError as e:
        return None, str(e)


def run_diff(old: RuleFile, new: RuleFile, *, limit: int = 3, timeout: float | None = None) -> list[Change]:
    """Every rule in either file with its behaviour change, then every edit to the
    invariants, require and ensures entries, result type and assumptions. Both versions of a rule are compiled
    against the new file's Env and compared under the assumptions the two files share
    (an assumption added in the new file can't hide a change)."""
    shared = [a for a in new.assumptions if a in old.assumptions]
    out = [
        _rule_change(new.env, name, old.rules.get(name), new.rules.get(name), shared, limit, timeout)
        for name in [*old.rules, *(n for n in new.rules if n not in old.rules)]
    ]
    for section in _CONDITIONS:
        before: dict[str, str] = getattr(old, section)
        after: dict[str, str] = getattr(new, section)
        for name in [*before, *(n for n in after if n not in before)]:
            a, b = before.get(name), after.get(name)
            if a != b:
                status = "added" if a is None else "removed" if b is None else "changed"
                out.append(Change(name, status, a, b, section=section))
    if old.returns != new.returns:
        status = "added" if old.returns is None else "removed" if new.returns is None else "changed"
        out.append(Change("returns", status, old.returns, new.returns, section="returns"))
    out += [Change(a, "removed", a, None, section="assumptions") for a in old.assumptions if a not in shared]
    out += [Change(a, "added", None, a, section="assumptions") for a in new.assumptions if a not in shared]
    return out


def _rule_change(
    env: Env,
    name: str,
    a: str | None,
    b: str | None,
    assuming: list[str],
    limit: int,
    timeout: float | None,
) -> Change:
    (pa, old_error), (pb, new_error) = _compile(env, a), _compile(env, b)
    if b is None:
        return Change(name, "removed", a, b)
    if pb is None:
        return Change(name, "invalid", a, b, reason=f"the new version doesn't compile: {new_error}")
    if a is None:
        return Change(name, "added", a, b)
    if pa is None:
        return Change(name, "added", a, b, reason=f"the old version didn't compile: {old_error}")
    if pa.canonical == pb.canonical:
        return Change(name, "unchanged", a, b)
    if "dyn" not in (pa.output_type, pb.output_type) and pa.output_type != pb.output_type:
        why = f"it now gives {pb.output_type}, not {pa.output_type}"
        return Change(name, "changed", a, b, reason=why)
    v = pa.equivalent(pb, assuming=assuming, timeout=timeout)
    if v.proved:
        return Change(name, "unchanged", a, b, reason="rewritten, but proved equivalent")
    if v.unknown:
        return Change(name, "undecided", a, b, reason=v.reason)
    diffs = pa.diff(pb, limit=limit, assuming=assuming, timeout=timeout)
    if not diffs and v.witness is not None:
        diffs = [Difference(v.witness, _value_or_error(pa, v.witness), _value_or_error(pb, v.witness))]
    examples = [Example(d.witness, _outcome(d.before), _outcome(d.after)) for d in diffs]
    return Change(name, "changed", a, b, examples)


def _conditions_changed(changes: list[Change]) -> bool:
    return any(c.section != "rules" for c in changes)


# -- output -----------------------------------------------------------------

_LEVEL = {"suspicious": "warning", "unverified": "warning"}


def _problem_json(p: Problem) -> dict[str, Any]:
    d: dict[str, Any] = {"kind": p.kind, "message": p.message}
    if p.invariant is not None:
        d["condition"] = p.invariant
    if p.verdict is not None and p.verdict.witness is not None:
        d["example"] = _jsonable(p.verdict.witness.relevant)
    return d


def _jsonable(v: Any) -> Any:
    return json.loads(json.dumps(v, default=str))


def _indent(s: str, prefix: str = "  ") -> str:
    return prefix + s.replace("\n", "\n" + prefix)


def _diff_lines(old: str | None, new: str | None) -> list[str]:
    """`- old` / `+ new` lines (`  ` for context), showing only what changed between
    multi-line versions."""
    a, b = (old or "").splitlines(), (new or "").splitlines()
    if old is not None and new is not None:
        body = list(difflib.unified_diff(a, b, lineterm="", n=max(len(a), len(b))))[3:]
        if body:
            return [f"{line[0]} {line[1:]}".rstrip() for line in body]
    return [f"- {x}" for x in a] + [f"+ {x}" for x in b]


def check_text(rf: RuleFile, results: dict[str, RuleCheck]) -> str:
    lines = []
    for n, r in results.items():
        lines.append(f"{rf.path}:{rf.line_of(n)}: {n}: {'ok' if r.ok else 'rejected'}")
        lines += [f"  - {p.message}".replace("\n", "\n    ") for p in r.problems]
    bad = sum(not r.ok for r in results.values())
    lines.append(f"{len(results) - bad} of {len(results)} rules proved ok" if results else "no rules")
    return "\n".join(lines)


def check_markdown(rf: RuleFile, results: dict[str, RuleCheck]) -> str:
    bad = {n: r for n, r in results.items() if not r.ok}
    head = f"### celspresso check: {_code(rf.path)}\n\n"
    if not bad:
        return head + f"All {len(results)} rules proved ok.\n"
    out = [head + f"**{len(bad)} of {len(results)} rules rejected.**\n"]
    for n, r in bad.items():
        out.append(f"#### {_code(n)}\n\n{_block('cel', r.source)}")
        out += [f"- **{p.kind}**: {_md(p.message)}" for p in r.problems]
        out.append("")
    return "\n".join(out)


def check_json(rf: RuleFile, results: dict[str, RuleCheck]) -> dict[str, Any]:
    return {
        "file": rf.path,
        "ok": all(r.ok for r in results.values()),
        "rules": {
            n: {"ok": r.ok, "line": rf.line_of(n), "problems": [_problem_json(p) for p in r.problems]}
            for n, r in results.items()
        },
    }


def diff_text(changes: list[Change]) -> str:
    lines = []
    for c in changes:
        if c.status == "unchanged" and c.reason is None:
            continue
        if c.status == "unchanged":
            lines.append(f"{c.label}: unchanged ({c.reason})")
            continue
        lines.append(f"{c.label}: {c.status}")
        if c.reason:
            lines.append(_indent(c.reason))
        if c.section != "rules":
            lines += [_indent(x) for x in _diff_lines(c.old, c.new)]
        lines += [f"  when {e.witness}: {e.old} -> {e.new}" for e in c.examples]
    return "\n".join(lines) or "no rule changed behaviour"


def diff_markdown(changes: list[Change], label: str) -> str:
    interesting = [c for c in changes if c.status != "unchanged"]
    head = f"### celspresso diff: {_code(label)}\n\n"
    if not interesting:
        n = len(changes)
        return head + f"No rule changed behaviour ({n} rule{'s' if n != 1 else ''} compared).\n"
    out = [head + _summary(changes) + "\n"]
    for c in interesting:
        title = {"rules": "", "assumptions": "assumption", "returns": "returns"}.get(
            c.section, _SINGULAR[c.section] + " "
        )
        if c.section not in ("assumptions", "returns"):
            title += _code(c.name)
        out.append(f"#### {title}: {c.status}\n")
        if c.old is not None and c.new is not None:
            out.append(_block("diff", "\n".join(_diff_lines(c.old, c.new))))
        else:
            out.append(_block("cel", c.new if c.new is not None else c.old or ""))
        if c.examples:
            out.append("| input | before | after |\n|---|---|---|")
            out += [
                f"| {_cell(_code(str(e.witness)))} | {_cell(e.old)} | **{_cell(e.new)}** |"
                for e in c.examples
            ]
            out.append("")
        if c.reason:
            out.append(f"> {_md(c.reason)}\n")
    return "\n".join(out)


def _summary(changes: list[Change]) -> str:
    counts: dict[str, int] = {}
    for c in changes:
        if c.section == "rules":
            counts[c.status] = counts.get(c.status, 0) + 1
    order = ("changed", "added", "removed", "undecided", "invalid", "unchanged")
    parts = [f"**{counts[s]} {s}**" if s != "unchanged" else f"{counts[s]} {s}" for s in order if s in counts]
    edits = sum(c.section != "rules" for c in changes)
    if edits:
        parts.append(f"**{edits} spec or assumption edit{'s' if edits != 1 else ''}**")
    return ", ".join(parts)


def _md(s: str) -> str:
    return s.replace("\n", "<br>")


def _cell(s: str) -> str:
    """Text safe inside a Markdown table cell."""
    return _md(s.replace("|", "\\|"))


def _code(s: str) -> str:
    """`s` as a Markdown code span, whatever backticks it contains."""
    fence = "`" * (max((len(r) for r in re.findall("`+", s)), default=0) + 1)
    pad = " " if s[:1] in ("`", " ") or s[-1:] in ("`", " ") else ""
    return f"{fence}{pad}{s}{pad}{fence}"


def _block(lang: str, s: str) -> str:
    """`s` as a fenced Markdown code block, whatever backticks it contains."""
    fence = "`" * max(3, max((len(r) + 1 for r in re.findall("`+", s)), default=0))
    return f"{fence}{lang}\n{s}\n{fence}\n"


def diff_json(changes: list[Change]) -> list[dict[str, Any]]:
    return [
        {
            "section": c.section,
            "name": c.name,
            "status": c.status,
            "old": c.old,
            "new": c.new,
            "reason": c.reason,
            "examples": [
                {"input": _jsonable(e.witness.relevant), "old": e.old, "new": e.new} for e in c.examples
            ],
        }
        for c in changes
    ]


Item = tuple[str, str, str, str, str]  # (section, name, kind, level, message)


def _artifact(path: str) -> dict[str, str]:
    """The SARIF artifact location: relative to the git repository's root when there is one."""
    p = Path(path).resolve()
    try:
        rel = p.relative_to(Path(_git_root(p)).resolve()).as_posix()
    except (OSError, subprocess.CalledProcessError, ValueError):
        return {"uri": Path(path).as_posix()}
    return {"uri": rel, "uriBaseId": "%SRCROOT%"}


def sarif(runs: list[tuple[RuleFile, list[Item]]]) -> dict[str, Any]:
    """SARIF 2.1.0, one result per item, for code scanning."""
    results = []
    kinds: dict[str, None] = {}
    for rf, items in runs:
        artifact = _artifact(rf.path)
        for section, name, kind, level, message in items:
            kinds[kind] = None
            results.append(
                {
                    "ruleId": kind,
                    "level": level,
                    "message": {"text": f"{name}: {message}"},
                    "locations": [
                        {
                            "physicalLocation": {
                                "artifactLocation": artifact,
                                "region": {"startLine": rf.line_of(name, section)},
                            }
                        }
                    ],
                }
            )
    driver = {
        "name": "celspresso",
        "version": __version__,
        "informationUri": "https://github.com/markberger/celspresso",
        "rules": [{"id": k, "shortDescription": {"text": k.replace("_", " ")}} for k in kinds],
    }
    return {
        "$schema": "https://json.schemastore.org/sarif-2.1.0.json",
        "version": "2.1.0",
        "runs": [{"tool": {"driver": driver}, "results": results}],
    }


def _check_items(results: dict[str, RuleCheck]) -> list[Item]:
    return [
        ("rules", n, p.kind, _LEVEL.get(p.kind, "error"), p.message)
        for n, r in results.items()
        for p in r.problems
    ]


def _diff_items(changes: list[Change]) -> list[Item]:
    items: list[Item] = []
    for c in changes:
        if c.section != "rules":
            what = " -> ".join(x for x in (c.old, c.new) if x is not None)
            kind = f"{_SINGULAR[c.section]}_{c.status}"
            items.append((c.section, c.name, kind, "note", f"{c.label} {c.status}: {what}"))
        elif c.status == "changed":
            ex = "; ".join(f"when {e.witness}: {e.old} -> {e.new}" for e in c.examples)
            items.append(("rules", c.name, "behaviour_changed", "note", f"behaviour changed: {ex}"))
        elif c.status in ("undecided", "invalid"):
            level = "error" if c.status == "invalid" else "warning"
            items.append(("rules", c.name, c.status, level, c.reason or c.status))
        elif c.status in ("added", "removed"):
            why = f" ({c.reason})" if c.reason else ""
            items.append(("rules", c.name, f"rule_{c.status}", "note", f"rule {c.status}{why}"))
    return items


# -- commands ---------------------------------------------------------------


def _need_rules(rf: RuleFile) -> None:
    if not rf.rules:
        raise UsageError(f"{rf.path}: no rules to check (the [rules] section is missing or empty)")


def cmd_check(args: argparse.Namespace, out: Callable[[str], None]) -> int:
    rf = load(args.file)
    _need_rules(rf)
    names = args.rule or None
    if names:
        missing = [n for n in names if n not in rf.rules]
        if missing:
            raise UsageError(f"{rf.path}: no rule named {', '.join(map(repr, missing))}")
    results = run_check(rf, names, args.timeout)
    if args.format == "json":
        out(json.dumps(check_json(rf, results), indent=2))
    elif args.format == "sarif":
        out(json.dumps(sarif([(rf, _check_items(results))]), indent=2))
    elif args.format == "markdown":
        out(check_markdown(rf, results))
    else:
        out(check_text(rf, results))
    return 0 if all(r.ok for r in results.values()) else 1


def cmd_diff(args: argparse.Namespace, out: Callable[[str], None]) -> int:
    if args.against is not None:
        if args.new is not None:
            raise UsageError("give either two files, or one file and --against REF")
        new = load(args.old)
        _need_rules(new)
        old_text = git_show(args.against, args.old)
        label = f"{args.old} ({args.against} → working tree)"
        old = (
            RuleFile(args.old, "", new.env, {})
            if old_text is None
            else load(args.old, text=old_text, env=new.env, validate=False)
        )
    else:
        if args.new is None:
            raise UsageError("diff needs two files (OLD NEW), or one file and --against REF")
        new = load(args.new)
        _need_rules(new)
        old = load(args.old, env=new.env, validate=False)
        label = f"{args.old} → {args.new}"
    changes = run_diff(old, new, limit=args.limit, timeout=args.timeout)
    everything = _conditions_changed(changes)
    names = (
        list(new.rules)
        if everything
        else [c.name for c in changes if c.section == "rules" and c.status in ("added", "changed")]
    )
    checks = run_check(new, names, args.timeout) if args.check else {}
    heading = (
        "checks on every rule (the spec or assumptions changed):"
        if everything
        else "checks on added and changed rules:"
    )
    if args.format == "json":
        payload: dict[str, Any] = {"changes": diff_json(changes)}
        if args.check:
            payload["check"] = check_json(new, checks)
        out(json.dumps(payload, indent=2))
    elif args.format == "sarif":
        out(json.dumps(sarif([(new, _diff_items(changes) + _check_items(checks))]), indent=2))
    elif args.format == "markdown":
        text = diff_markdown(changes, label)
        if checks:
            text += "\n" + check_markdown(new, checks)
        out(text)
    else:
        text = diff_text(changes)
        if checks:
            text += f"\n\n{heading}\n" + check_text(new, checks)
        out(text)
    failed = any(not r.ok for r in checks.values()) or any(
        c.status in ("invalid", "undecided") for c in changes
    )
    changed = any(c.status != "unchanged" for c in changes)
    return 1 if failed or (args.fail_on_change and changed) else 0


def _parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(
        prog="celspresso", description="Type-check and formally verify CEL rule files."
    )
    p.add_argument("--version", action="version", version=f"celspresso {__version__}")
    sub = p.add_subparsers(dest="command", required=True)
    fmt: dict[str, Any] = {
        "choices": ["text", "markdown", "json", "sarif"],
        "default": "text",
        "help": "output format (default: text)",
    }
    timeout: dict[str, Any] = {"type": float, "default": None, "help": "seconds per solver query"}

    c = sub.add_parser(
        "check",
        help="prove each rule can fire, can't fail, and keeps the invariants (or, for a value, the ensures)",
    )
    c.add_argument("file", help="rule file (.toml, .json, .yaml)")
    c.add_argument("--rule", action="append", help="check only this rule (repeatable)")
    c.add_argument("--format", **fmt)
    c.add_argument("--timeout", **timeout)
    c.set_defaults(run=cmd_check)

    d = sub.add_parser("diff", help="show, with example inputs, how each rule's behaviour changed")
    d.add_argument("old", help="the old rule file (or the only file, with --against)")
    d.add_argument("new", nargs="?", help="the new rule file")
    d.add_argument("--against", metavar="REF", help="compare the file with its version at git revision REF")
    d.add_argument("--limit", type=int, default=3, help="example inputs per changed rule (default: 3)")
    d.add_argument(
        "--no-check",
        dest="check",
        action="store_false",
        help="don't check added/changed rules (or every rule, when the file's conditions changed)",
    )
    d.add_argument(
        "--fail-on-change",
        action="store_true",
        help="exit 1 if any rule's behaviour, the spec or an assumption changed",
    )
    d.add_argument("--format", **fmt)
    d.add_argument("--timeout", **timeout)
    d.set_defaults(run=cmd_diff)
    return p


def main(argv: Sequence[str] | None = None) -> int:
    args = _parser().parse_args(argv)
    try:
        return args.run(args, print)
    except UsageError as e:
        print(f"celspresso: {e}", file=sys.stderr)
        return 2
    except Exception as e:  # noqa: BLE001 - a crash must never look like "rule rejected" (exit 1)
        print(f"celspresso: internal error: {type(e).__name__}: {e}", file=sys.stderr)
        return 2


if __name__ == "__main__":  # pragma: no cover
    sys.exit(main())
