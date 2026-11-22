"""Load tests for the celspresso verifier.

Run:  uv run maturin develop --release && uv run python benchmarks/bench_verify.py [--quick]

Reports wall-clock latency per query (median / p95 / max), the solver-reported
time, the verdict status, and throughput under thread concurrency.
"""

from __future__ import annotations

import argparse
import datetime as dt
import os
import platform
import statistics
import sys
import time
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
from typing import TYPE_CHECKING, Annotated, Any, Literal

from pydantic import BaseModel, Field

from celspresso import Env, RuleSet, Verdict

if TYPE_CHECKING:
    from collections.abc import Callable

# -- schemas ------------------------------------------------------------------


class Address(BaseModel):
    zip: Annotated[str, Field(min_length=5, max_length=5, pattern=r"^[0-9]+$")]
    state: Literal["CA", "NY", "TX", "WA"]


class Patient(BaseModel):
    age: Annotated[int, Field(ge=0, le=130)]
    dob: dt.date
    tier: Literal["bronze", "silver", "gold"]
    codes: Annotated[list[str], Field(max_length=6)]
    charges: Annotated[list[Annotated[int, Field(ge=0, le=1_000_000)]], Field(max_length=6)]
    email: Annotated[str, Field(max_length=40)]
    nickname: str | None = None
    address: Address


ENV = Env(p=Patient, today=dt.date).table("covered", {"99213", "99214", "J3490", "A0428"})


def lst(n: int) -> Env:
    return Env(xs=Annotated[list[Annotated[int, Field(ge=-1000, le=1000)]], Field(max_length=n)])


# -- harness ------------------------------------------------------------------


def measure(fn: Callable[[], Verdict | Any], runs: int, warmup: int = 2) -> dict[str, Any]:
    for _ in range(warmup):
        fn()
    walls: list[float] = []
    solver: list[float] = []
    statuses: Counter[str] = Counter()
    for _ in range(runs):
        t0 = time.perf_counter()
        out = fn()
        walls.append((time.perf_counter() - t0) * 1000)
        if isinstance(out, Verdict):
            statuses[out.status.name] += 1
            solver.append(out.stats.elapsed_ms)
        else:
            statuses["ok"] += 1
    walls.sort()
    return {
        "median": statistics.median(walls),
        "p95": walls[min(len(walls) - 1, int(len(walls) * 0.95))],
        "max": walls[-1],
        "solver": statistics.median(solver) if solver else float("nan"),
        "status": "/".join(f"{k}" if len(statuses) == 1 else f"{k}:{v}" for k, v in statuses.items()),
    }


def table(title: str, rows: list[tuple[str, dict[str, Any]]]) -> None:
    print(f"\n## {title}\n")
    print(
        f"| {'case':<52} | {'status':<10} | {'median ms':>9} | {'p95 ms':>8} | {'max ms':>8} | {'solver ms':>9} |"
    )
    print(f"|{'-' * 54}|{'-' * 12}|{'-' * 11}|{'-' * 10}|{'-' * 10}|{'-' * 11}|")
    for name, r in rows:
        print(
            f"| {name:<52} | {r['status']:<10} | {r['median']:>9.2f} | {r['p95']:>8.2f} | "
            f"{r['max']:>8.2f} | {r['solver']:>9.2f} |"
        )


# -- scenarios ----------------------------------------------------------------


def single_queries(runs: int) -> None:
    pred = ENV.predicate
    adult = pred("p.age >= 18")
    eligible = pred("p.age >= 18 && p.tier != 'bronze' && p.codes.all(c, c in covered) && size(p.codes) > 0")
    eligible2 = pred(
        "size(p.codes) > 0 && p.codes.all(c, c in covered) && !(p.tier == 'bronze') && 18 <= p.age"
    )
    cases: list[tuple[str, Callable[[], Any]]] = [
        ("compile (parse + check)", lambda: ENV.compile("p.age >= 18 && p.tier == 'gold'")),
        ("evaluate", lambda: eligible.evaluate(SAMPLE)),
        ("int: sat  p.age > 200 (schema)", pred("p.age > 200").satisfiable),
        ("int: always_true  age>=18 => age>=10", lambda: adult.implies("p.age >= 10")),
        ("int: refuted  age >= 18 always", adult.always_true),
        ("int: division can_error", ENV.compile("1000 / (p.age - 40)").can_error),
        ("enum: tier == 'platinum'", pred("p.tier == 'platinum'").satisfiable),
        (
            "string: startsWith/endsWith/size",
            pred(
                "p.email.endsWith('@example.com') && p.email.startsWith('a') && size(p.email) < 20"
            ).satisfiable,
        ),
        (
            "string: regex email-ish matches",
            pred("p.email.matches('^[a-z]+@[a-z]+\\\\.(com|org)$')").satisfiable,
        ),
        ("string: pattern zip contradicts", pred("p.address.zip.contains('x')").satisfiable),
        (
            "list: all/exists over codes (max 6)",
            pred("p.codes.exists(c, c == '99213') && p.codes.all(c, c in covered)").satisfiable,
        ),
        ("list: sum(charges) > 5M impossible", pred("p.charges.sum() > 6000000").satisfiable),
        ("list: equivalence reordered rule", lambda: eligible.equivalent(eligible2)),
        ("nullable: nickname present & long", pred("p.nickname != null && size(p.nickname) > 3").satisfiable),
        (
            "date: ageOn consistent with age",
            pred(
                "p.dob.ageOn(today) >= 18 && today == date('2026-01-01') && p.dob > date('2010-01-01')"
            ).satisfiable,
        ),
        (
            "date: implies year bound",
            lambda: pred("today == date('2026-06-01') && p.dob.ageOn(today) >= 65").implies(
                "p.dob.year() <= 1961"
            ),
        ),
    ]
    table("Single queries (Patient schema)", [(n, measure(f, runs)) for n, f in cases])


def scaling_clauses(runs: int) -> None:
    env = Env({f"v{i}": Annotated[int, Field(ge=0, le=1000)] for i in range(400)})
    rows = []
    for n in (5, 25, 100, 400):
        conj = " && ".join(f"v{i} > {i % 997}" for i in range(n))
        rev = " && ".join(f"{i % 997} < v{i}" for i in reversed(range(n)))
        a, b = env.predicate(conj), env.predicate(rev)
        rows.append((f"{n:>3} clauses: satisfiable", measure(a.satisfiable, runs)))
        rows.append(
            (f"{n:>3} clauses: equivalent (reordered)", measure(lambda a=a, b=b: a.equivalent(b), runs))
        )
    table("Scaling: expression size", rows)


def scaling_lists(runs: int) -> None:
    rows = []
    for n in (4, 8, 16, 32, 64):
        env = lst(n)
        p = env.predicate("xs.all(x, x > 0)")
        rows.append(
            (
                f"max_length={n:>2}: all>0 => sum>=size",
                measure(lambda p=p: p.implies("xs.sum() >= size(xs)"), runs),
            )
        )
        rows.append(
            (
                f"max_length={n:>2}: exists/all contradiction",
                measure(env.predicate("xs.exists(x, x > 5) && xs.all(x, x < 3)").satisfiable, runs),
            )
        )
        rows.append(
            (
                f"max_length={n:>2}: filter/map size",
                measure(env.predicate("xs.filter(x, x > 0).map(x, x * 2).all(y, y > 0)").always_true, runs),
            )
        )
    table("Scaling: list length (exact, no unroll bound)", rows)


def batch_ops(runs: int) -> None:
    pred = ENV.predicate
    rules = {f"age_band_{i}": pred(f"p.age >= {i * 10} && p.age < {(i + 1) * 10}") for i in range(14)}
    rules["dead"] = pred("p.age > 140")
    rules["gold_adult"] = pred("p.tier == 'gold' && p.age >= 18")
    rs = RuleSet(rules)
    n_pairs = len(rules) * (len(rules) - 1) // 2
    old, new = pred("p.age >= 18 && p.tier != 'bronze'"), pred("p.age >= 21 && p.tier == 'gold'")
    rows = [
        (f"RuleSet.unreachable ({len(rules)} rules)", measure(rs.unreachable, max(3, runs // 5), 1)),
        (
            f"RuleSet overlap check_pairwise ({n_pairs} pairs)",
            measure(lambda: rs.check_pairwise(lambda a, b: (a & b).satisfiable()), max(3, runs // 10), 1),
        ),
        ("diff(limit=10)", measure(lambda: old.diff(new, limit=10), max(3, runs // 5), 1)),
    ]
    table("Batch operations", rows)


def concurrency(total: int) -> None:
    pred = ENV.predicate
    queries = [
        pred("p.codes.exists(c, c == '99213') && p.codes.all(c, c in covered)").satisfiable,
        pred("p.email.endsWith('@example.com') && size(p.email) < 20").satisfiable,
        lambda: pred("p.age >= 21").implies("p.age >= 18"),
        pred("p.charges.sum() > 6000000").satisfiable,
    ]
    print("\n## Throughput under concurrency (mixed queries, GIL released while solving)\n")
    print("| threads | queries | wall s | queries/s | speedup |")
    print("|--------:|--------:|-------:|----------:|--------:|")
    base = None
    for threads in (1, 2, 4, 8):
        t0 = time.perf_counter()
        with ThreadPoolExecutor(threads) as ex:
            list(ex.map(lambda i: queries[i % len(queries)](), range(total)))
        wall = time.perf_counter() - t0
        qps = total / wall
        base = base or qps
        print(f"| {threads:>7} | {total:>7} | {wall:>6.2f} | {qps:>9.1f} | {qps / base:>6.2f}x |")


SAMPLE = {
    "p": Patient(
        age=40,
        dob=dt.date(1985, 3, 1),
        tier="gold",
        codes=["99213"],
        charges=[100],
        email="a@example.com",
        address=Address(zip="94110", state="CA"),
    ),
    "today": dt.date(2026, 1, 1),
}


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--quick", action="store_true", help="fewer repetitions")
    args = ap.parse_args()
    runs = 5 if args.quick else 30
    print("# celspresso verifier load test\n")
    print(f"- machine: {platform.machine()} {platform.processor() or ''}, {os.cpu_count()} cores")
    print(f"- python {sys.version.split()[0]}, runs per case: {runs} (+2 warmup)")
    single_queries(runs)
    scaling_clauses(max(3, runs // 3))
    scaling_lists(max(3, runs // 3))
    batch_ops(runs)
    concurrency(80 if args.quick else 400)


if __name__ == "__main__":
    main()
