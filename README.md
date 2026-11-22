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
| `env.check_rule(src, invariants)` | Is this rule safe to accept? | report |

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

The report is plain text that a person or an LLM can act on, so it can drive a repair loop:

```python
feedback = ""
for _ in range(5):
    src = llm.draft_rule(policy_doc, feedback)   # your LLM call
    report = env.check_rule(src, POLICY)
    if report.ok:
        break
    feedback = str(report)
```

`report.ok` means *proved*: a check that comes back `UNKNOWN` is a problem, never a pass. For a fuller example, see [`examples/credentialing.py`](examples/credentialing.py), where an agent drafts provider-scheduling rules for a healthcare back office against compliance invariants.

## Verdicts are never guesses

- **Every counterexample is real.** It is replayed through the evaluator and validated by your Pydantic model before you see it.
- **`UNKNOWN` can't be mistaken for an answer.** `bool(verdict)` raises, and `verdict.reason` names the timeout or the construct that isn't modeled yet.
- **The semantics are CEL's.** Integers are 64-bit with overflow errors, division truncates toward zero, and `&&` and `||` absorb errors. Your schema's `ge`, `le`, `max_length`, `Literal` and `Enum` become facts the prover relies on.

## How it compares

| | evaluate | type-check | prove & find counterexamples |
|---|:-:|:-:|:-:|
| [`common-expression-language`](https://pypi.org/project/common-expression-language/) | ✓ | | |
| [`cel-python`](https://github.com/cloud-custodian/cel-python) | ✓ | | |
| **celspresso** | ✓ | ✓ | ✓ |

A Rust core parses, checks and evaluates CEL, and encodes its exact semantics into [Z3](https://github.com/Z3Prover/z3). A typical proof takes 2–20 ms, and the GIL is released while solving.

## More

- **Types:** Pydantic models, dataclasses, `Optional`, lists, maps, `date`, timezone-aware `datetime` and `timedelta`. Store money as integer cents; `Decimal` is rejected.
- **Extensions:** strings, math, lists, sets, base64, optionals, `cel.bind`, `cel.block` and the Kubernetes network library.
- **Your own building blocks:** `env.define(...)` for named sub-expressions, `env.table(...)` for lookup tables and `@function` for Python functions.
- **Debugging and tests:** `expr.explain(data)` shows the value of every sub-expression; `celspresso.testing` has `assert_equivalent`, `assert_implies`, `assert_never` and more.
- **Not yet supported:** protobuf messages and JSON values. The verifier doesn't yet model doubles, maps, bytes, optionals or timestamps; those return `UNKNOWN` with the reason.
- **Contributing:** `scripts/check.sh` runs every lint, type-check and test gate.

## License

[Apache-2.0](LICENSE)
