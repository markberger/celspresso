# celspresso ☕

**Find the input that breaks your business rules, before your customers do.**

celspresso type-checks, evaluates, and *proves things about* [CEL](https://cel.dev) rules from Python. CEL is the expression language behind Kubernetes, Google Cloud IAM and Envoy. Rules are usually tested on a handful of examples; celspresso checks them against every possible input and hands you the one that breaks them.

```python
from typing import Annotated, Literal
from pydantic import BaseModel, Field
from celspresso import Env

class Order(BaseModel):
    total_cents: Annotated[int, Field(ge=0)]
    days_since_delivery: Annotated[int, Field(ge=0, le=365)]
    status: Literal["delivered", "lost", "damaged"]
    tier: Literal["standard", "gold"]

env = Env(order=Order)
auto_refund = env.predicate("""
    order.status == 'lost'
    || (order.status == 'damaged' && order.days_since_delivery <= 30)
    || (order.tier == 'gold' && order.total_cents < 5000)
""")

# Finance's one requirement: never auto-refund more than $500.
print(auto_refund.implies("order.total_cents <= 50000").counterexample)
# order.days_since_delivery = 0, order.status = 'damaged', order.tier = 'standard', order.total_cents = 50001
```

Every test passed. The prover found the gap in milliseconds: a damaged $500.01 order is refunded with no cap.

It works just as well on rules you didn't write, [from customers, an admin UI, or an LLM](#accepting-rules-you-didnt-write).

## Install

> **Pre-alpha.** Not on PyPI yet, and the API may still change.

You need Rust (stable) and [uv](https://docs.astral.sh/uv/). Z3 is downloaded and linked statically.

```sh
git clone https://github.com/markberger/celspresso && cd celspresso
uv sync --group dev && uv run maturin develop --release
```

## What you can ask

| | Question | Answer |
|---|---|---|
| `p.satisfiable()` | Can this ever be true? | `SAT` + example / `UNSAT` |
| `p.always_true()` | Is it true for every valid input? | `PROVED` / `REFUTED` + counterexample |
| `a.implies(b)` | Whenever `a` holds, does `b`? | `PROVED` / `REFUTED` + counterexample |
| `a.equivalent(b)` | Do they agree on every input, errors included? | `PROVED` / `REFUTED` + counterexample |
| `a.diff(b)` | Where do they disagree, and why? | one input per distinct reason |
| `e.can_error()` | Can evaluation fail (÷0, overflow, missing key)? | `SAT` + example / `UNSAT` |
| `e.bounds()` | What's the smallest and largest value it can take? | proved `[min, max]` + an input for each |
| `env.check_rule(src, invariants, require=...)` | Is this rule safe, and useful enough, to accept? | report |

**Catch a refactor that changes behavior.** Someone tidies `<= 30` into `< 30`:

```python
auto_refund.equivalent(tidied).counterexample
# order.days_since_delivery = 30, order.status = 'damaged', ...
```

**Review behavior, not code.** A proposed "simplification", explained as the cases that change:

```python
looser = env.predicate("order.status != 'delivered' || (order.tier == 'gold' && order.total_cents < 10000)")
for case in auto_refund.diff(looser):
    print(case)
# order.days_since_delivery = 31, order.status = 'damaged', order.tier = 'standard', ...
# order.days_since_delivery = 31, order.status = 'damaged', order.tier = 'gold', order.total_cents = 5000
# order.days_since_delivery = 0, order.status = 'delivered', order.tier = 'gold', order.total_cents = 5000
```

**Typos fail at compile time**, not in production:

```
>>> env.compile("order.totl_cents > 0")
CelTypeError: 1:1: undefined field 'totl_cents' on Order (did you mean 'total_cents'?)
  | order.totl_cents > 0
  | ^^^^^^^^^^^^^^^^
```

And `auto_refund.evaluate({"order": order})` runs the rule in about 10 µs.

## Accepting rules you didn't write

When rules come from customers, operations teams or an LLM, `check_rule` decides whether to accept them. It checks that a rule compiles, can fire, can't fail at runtime, and never breaks the invariants *you* own:

```python
POLICY = {
    "refunds over $500 need a human": "order.total_cents <= 50000",
    "nothing is refunded after 90 days": "order.days_since_delivery <= 90",
}

print(env.check_rule("order.status == 'lost' || (order.tier == 'gold' && order.days_since_delivery <= 120)", POLICY))
# rejected:
# - violates 'refunds over $500 need a human' when order.status = 'lost', order.total_cents = 50001, ...
# - violates 'nothing is refunded after 90 days' when order.days_since_delivery = 91, order.status = 'lost', ...
```

Invariants keep a rule *safe*. `require=` and `examples=` keep it *useful*. Without them, a rule that refunds almost nothing passes every safety check:

```python
MUST_REFUND = {"small lost orders": "order.status == 'lost' && order.total_cents <= 10000"}

rule = "order.status == 'lost' && order.total_cents == 700 && order.days_since_delivery <= 90"
print(env.check_rule(rule, POLICY, require=MUST_REFUND))
# rejected:
# - too narrow: doesn't allow 'small lost orders', e.g. when order.days_since_delivery = 91, order.status = 'lost', order.total_cents = 0
```

`check_rule` also flags code that type-checks but can't be what was meant. For example, `order.tier == 'Gold'` can never be true when the tier is `'standard'` or `'gold'`. Habits from other languages get a pointer to the CEL form: `and` → `&&`, `len(x)` → `size(x)`, `None` → `null`.

`env.describe()` gives an LLM everything it needs in one block of text: variables, fields, types and constraints, functions, definitions and a CEL cheat sheet. The report is plain text too, so the two drive a repair loop:

```python
spec, feedback = env.describe(), ""
for _ in range(5):
    src = llm.draft_rule(spec, policy_doc, feedback)   # your LLM call
    report = env.check_rule(src, POLICY, require=MUST_REFUND, examples=golden_set)
    if report.ok:
        break
    feedback = str(report)
```

`report.ok` means *proved*: a check that comes back `UNKNOWN` is a problem, never a pass. For a fuller example, see [`examples/credentialing.py`](examples/credentialing.py), where an agent drafts provider-scheduling rules for a healthcare back office against compliance invariants.

## Rule files and code review

Rules that live in your repository can be checked from the command line. A rule file (TOML, JSON, or YAML with PyYAML installed) names the variables' types and lists the rules, the invariants no rule may break, and optionally the cases every rule must allow:

```toml
# examples/refunds/rules.toml
vars = { order = "models:Order" }     # module:attribute; or env = "policy:env" for a full Env

[rules]
damaged = "order.status == 'damaged' && order.days_since_delivery <= 30 && order.total_cents <= 50000"
lost = "order.status == 'lost' && order.days_since_delivery <= 60 && order.total_cents <= 20000"

[invariants]
capped = "order.total_cents <= 50000"
recent = "order.days_since_delivery <= 90"
```

`celspresso check rules.toml` runs `check_rule` on every rule and exits non-zero if any is rejected. `celspresso diff rules.toml --against main` compares each rule with its version at a git revision. Instead of a text diff, it reports what the change *does*:

```
$ celspresso diff rules.toml --against main
damaged: unchanged (rewritten, but proved equivalent)
lost: changed
  when order.days_since_delivery = 0, order.status = 'damaged', order.total_cents = 0: false -> true
  when order.days_since_delivery = 0, order.status = 'lost', order.total_cents = 20001: false -> true

checks on added and changed rules:
rules.toml:7: lost: rejected
  - violates 'capped' when order.days_since_delivery = 0, order.status = 'damaged', order.total_cents = 50001
0 of 1 rules proved ok
```

Old and new rules are compared only under the assumptions both versions share, so adding an assumption can't hide a change. Edits to the invariants, `require` entries or assumptions are listed too, and then every rule is rechecked, not just the added and changed ones (`--no-check` skips the checks). A file renamed in git has no old version under its new path, so all its rules show as `added`.

Both commands take `--format markdown` (for a pull-request comment), `json`, or `sarif` (for GitHub code scanning). Rewrites the prover can't decide are reported as `undecided`, never as unchanged. Exit status:

- **0**: everything was proved.
- **1**: `check` rejected a rule; or `diff` found a rule in the new file that is invalid or undecided, or that fails its check. With `--fail-on-change`, `diff` also exits 1 on any change to a rule's behaviour, an invariant, a `require` entry or an assumption.
- **2**: the command line or the file can't be used, for example a file with no rules or a condition that doesn't compile. Internal errors also exit 2, so a crash never looks like a rejected rule.

## Verdicts are never guesses

- **Every counterexample is real.** It is replayed through the evaluator and validated by your Pydantic model before you see it.
- **`UNKNOWN` can't be mistaken for an answer.** `bool(verdict)` raises, and `verdict.reason` names the timeout or the construct that isn't modeled yet.
- **The semantics are CEL's.** Integers are 64-bit with overflow errors, division truncates toward zero, and `&&` and `||` absorb errors. Your schema's `ge`, `le`, `max_length`, `Literal` and `Enum` become facts the prover relies on, and `evaluate()` rejects inputs that break them, so a rule never runs on data its proofs don't cover. For rules you didn't write, `Env(..., limits=Limits(max_cost=...))` caps evaluation cost.

## How it compares

| | evaluate | type-check | prove & find counterexamples |
|---|:-:|:-:|:-:|
| [`common-expression-language`](https://pypi.org/project/common-expression-language/) | ✓ | | |
| [`cel-python`](https://github.com/cloud-custodian/cel-python) | ✓ | | |
| **celspresso** | ✓ | ✓ | ✓ |

A Rust core parses, checks and evaluates CEL, and encodes its exact semantics into [Z3](https://github.com/Z3Prover/z3). Proofs about numbers, enums, dates and string prefixes or suffixes typically take 2–20 ms, and the GIL is released while solving. Rules that mix `contains` and regexes can take hundreds of milliseconds. Some regex questions reach the timeout and come back `UNKNOWN`, never with a wrong answer.

## More

- **Types:** Pydantic models, dataclasses, `Optional`, lists, maps, `date`, timezone-aware `datetime` and `timedelta`. Store money as integer cents; `Decimal` is rejected. Types without a Python class (an ORM's models, a historical schema, two versions of one model) can be declared directly with `celspresso.schema`: `Env(structs=[Struct("Order", [Field("total", T.int, Constraints(ge=0))])], order=T.struct("Order"))`. To teach celspresso a whole type system (an ORM, protobuf), write a `celspresso.adapters.TypeAdapter` and pass `Env(adapters=[...])`; Pydantic and dataclass support are built the same way. A field whose value isn't a plain attribute or key (a related-object manager, a renamed column) takes a `reader=` callable.
- **`None` is `null`:** an `Optional` field holding `None` is `null` in CEL, and `has(m.f)` is false for it. Guard with `has(m.note) && m.note.startsWith('x')` or `m.note != null && ...`. Calling a method on `null` is an evaluation error.
- **Extensions:** strings, math, lists, sets, base64, optionals, `cel.bind`, `cel.block` and the Kubernetes network library.
- **Your own building blocks:** `env.define(...)` for named sub-expressions, `env.table(...)` for lookup tables and `@function` for Python functions. The prover never runs your Python while it solves. Each function is handled in one of three ways:
  - **Written in CEL**, so it is fully verified: `env.define("clamp", "v < 0 ? 0 : (v > 100 ? 100 : v)", params={"v": int})`, called as `clamp(x)`.
  - **Tabulated automatically** when every parameter is a `bool`, `Literal`, `Enum` or bounded int (at most 1024 inputs in total). It is called once per input when declared and is then known exactly. Opt out with `tabulate=False`.
  - **Opaque** otherwise. Tell the prover what holds with `@function(ensures="result >= 0 && result <= 100", total=True)`. If an answer depends on what the function returns, the verdict is `UNKNOWN`, and its reason says which of these three ways would fix that.
- **Rule sets:** `RuleSet({...}).verify_all(invariants)` vets every rule at once; `unreachable()`, `can_error()` and `check_pairwise(...)` find dead, crashing and overlapping rules.
- **Debugging and tests:** `expr.explain(data)` shows the value of every sub-expression; `celspresso.testing` has `assert_equivalent`, `assert_implies`, `assert_never` and more.
- **Not yet supported:** protobuf messages and JSON values. Fields typed `Any` or `dict[str, Any]` can be evaluated, but the verifier can't see into them: checks that depend on them return `UNKNOWN`, and the reason suggests a concrete type. The verifier models ints, doubles (IEEE, NaN included), strings, lists, maps, optionals, dates, timestamps and durations; bytes and named time zones return `UNKNOWN` with the reason. Proofs over a list or map need a `max_length` (or a larger `unroll_limit`), so the prover can cover every length.
- **Contributing:** `scripts/check.sh` runs every lint, type-check and test gate. Install the hooks once with `uv run prek install && ln -sf ../../scripts/pre-push .git/hooks/pre-push`. Commits then get file hygiene, ruff and rustfmt fixes on the staged files. Pushes run `scripts/check.sh --fast` on the pushed commit, and refuse while the tree has uncommitted files.

## License

[Apache-2.0](LICENSE)
