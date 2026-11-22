# celspresso

**Typed [CEL](https://cel.dev) expressions for Python, with a built-in prover.**

Business rules live in config, change weekly, and are tested on a handful of examples. celspresso checks them against *every possible input*, and when a rule is wrong, it hands you the input that breaks it.

Say support auto-approves refunds with this rule, and finance has one requirement: **never auto-refund more than $500.**

```python
from typing import Annotated, Literal
from pydantic import BaseModel, Field
from celspresso import Env

class Order(BaseModel):
    total_cents: Annotated[int, Field(ge=0)]
    items: Annotated[int, Field(ge=0, le=100)]
    days_since_delivery: Annotated[int, Field(ge=0, le=365)]
    status: Literal["delivered", "lost", "damaged"]
    tier: Literal["standard", "gold"]

env = Env(order=Order)

auto_refund = env.predicate("""
    order.status == 'lost'
    || (order.status == 'damaged' && order.days_since_delivery <= 30)
    || (order.tier == 'gold' && order.total_cents < 5000)
""")

auto_refund.implies("order.total_cents <= 50000")
# Verdict(REFUTED, counterexample={'order': {'status': 'damaged', 'total_cents': 50001,
#                                            'days_since_delivery': 0, 'tier': 'standard', 'items': 0}})
```

Every test you wrote probably passed. The prover found the gap in milliseconds: a damaged $500.01 order is refunded with no cap.

Under the hood, a Rust core parses and type-checks CEL, evaluates it in microseconds, and encodes its exact semantics into [Z3](https://github.com/Z3Prover/z3). Your Pydantic constraints (`ge`, `le`, `Literal`, ...) become facts the prover can rely on.

> **Status: pre-alpha.** Not on PyPI yet, and the API may still change.

## Install

From source. You need Rust (stable) and [uv](https://docs.astral.sh/uv/). Z3 is downloaded and linked statically, so you don't need a system install.

```sh
git clone https://github.com/markberger/celspresso && cd celspresso
uv sync --group dev
uv run maturin develop --release
```

## A tour

Continuing with the refund rule above.

**Evaluate it**, in microseconds:

```python
auto_refund.evaluate({"order": order})   # True
```

**Catch a refactor that changes behavior.** Someone "tidies up" the rule, and `<= 30` quietly becomes `< 30`:

```python
tidied = env.predicate("""
    order.status == 'lost'
    || (order.status == 'damaged' && order.days_since_delivery < 30)
    || (order.tier == 'gold' && order.total_cents < 5000)
""")
auto_refund.equivalent(tidied)
# Verdict(REFUTED, counterexample={'order': {'status': 'damaged', 'days_since_delivery': 30, ...}})
```

The counterexample is exactly the boundary case: a customer whose damaged order arrived 30 days ago.

**Find inputs that crash an expression** before production does:

```python
env.expr("order.total_cents / order.items", int).can_error()
# Verdict(SAT, witness={'order': {'items': 0, ...}})
```

**Find dead rules** that can never fire, given your schema:

```python
from celspresso import RuleSet

RuleSet({
    "lost":        env.predicate("order.status == 'lost'"),
    "late_damage": env.predicate("order.status == 'damaged' && order.days_since_delivery > 400"),
}).unreachable()
# {'late_damage': Verdict(UNSAT)}   # the schema caps days_since_delivery at 365
```

**Typos fail at compile time**, not in production:

```python
env.compile("order.totl_cents > 0")
# CelTypeError: 1:1: undefined field 'totl_cents' on Order (did you mean 'total_cents'?)
#   | order.totl_cents > 0
#   | ^^^^^^^^^^^^^^^^
```

**Counterexamples are real objects.** `verdict.counterexample.to_python()` returns `{'order': Order(...)}`, ready to paste into a regression test.

### What you can ask

| Method | Question | Answers |
|---|---|---|
| `p.satisfiable()` | Can this ever be true? | `SAT` + witness / `UNSAT` |
| `p.always_true()` | Is this true for every valid input? | `PROVED` / `REFUTED` + counterexample |
| `a.implies(b)` | Whenever `a` holds, does `b`? | `PROVED` / `REFUTED` |
| `a.equivalent(b)` | Do these agree on every input, errors included? | `PROVED` / `REFUTED` |
| `e.can_error()` | Can evaluation fail (÷0, overflow, missing key)? | `SAT` + witness / `UNSAT` |
| `a.diff(b, limit=5)` | Show me inputs where these disagree | list of witnesses |

Every method takes `assuming=` for extra preconditions and `timeout=` in seconds. `RuleSet` runs checks across a whole collection of rules: unreachable rules, overlapping rules, and old-vs-new diffs.

## Verdicts are never guesses

- **`bool(verdict)` raises.** A query can come back `UNKNOWN` because of a timeout or a construct that isn't modeled yet. That should never be silently read as yes or no. Use `.proved`, `.refuted`, `.sat`, `.unsat`, `.unknown`, or `.expect()`, which raises with a readable report.
- **Every witness is real.** Before you see a witness, it is replayed through the evaluator and validated by your Pydantic model. If either check fails, the result is downgraded to `UNKNOWN`, and `verdict.reason` explains why.
- **The semantics are CEL's, not Python's.** Integers are 64-bit with overflow errors. Division truncates toward zero. `&&` and `||` absorb errors in both directions.
- **Your schema is part of the question.** `ge`, `le`, `max_length`, `pattern`, `Literal` and `Enum` become assumptions. Turn this off with `Env(..., schema_constraints=False)`.

## Beyond the basics

- `env.define("recent", "order.days_since_delivery <= 30")` adds a named, reusable sub-expression.
- `env.table("covered", {"99213", "99214"})` adds a constant lookup table.
- `@function` and `env.extend(functions=[...])` call your own Python functions from CEL.
- `expr.explain(data)` shows the value of every sub-expression, for debugging and audit logs.
- `celspresso.testing` provides `assert_equivalent`, `assert_implies`, `assert_never` and more for your test suite.
- Pydantic models, dataclasses, `Optional`, lists, maps and `datetime.date` are all supported. `Decimal` is rejected: store money as integer cents.

## Performance

Measured on an Apple M3:

- Evaluating takes about 10 µs.
- A typical proof or counterexample takes 2–20 ms.
- Large lists (`max_length` ≥ 16) take 100–200 ms.
- The GIL is released while solving, so verification scales across threads.

Reproduce these numbers with `uv run python benchmarks/bench_verify.py`.

## Not yet supported

Protobuf messages, doubles, maps and bytes inside the verifier, timestamps and durations, and function contracts. Constructs the verifier doesn't model yet return `UNKNOWN`, with the reason named in `verdict.reason`.

## Contributing

```sh
scripts/check.sh   # ruff, pyright, pytest and Rust tests, with coverage gates
```

## License

[Apache-2.0](LICENSE)
