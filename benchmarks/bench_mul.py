"""Integer multiplication benchmark: nonlinear questions under tight, wide and no bounds.

Run:  uv run maturin develop --release && uv run python benchmarks/bench_mul.py

Products of two variables are nonlinear (undecidable in general). The subset keeps them,
so this tracks how often the verifier still decides them, and how fast. Factoring-style
questions with wide bounds are expected to time out.
"""

from __future__ import annotations

import time
from typing import Annotated

from pydantic import Field

from celspresso import Env


def bounded(lo: int, hi: int) -> object:
    return Annotated[int, Field(ge=lo, le=hi)]


PROFILES = {"tight": bounded(0, 1000), "wide": bounded(-(10**9), 10**9), "int64": int}
CASES = [
    ("equiv", "a * b", "b * a"),
    ("equiv", "a * (b + c)", "a * b + a * c"),
    ("equiv", "(a + b) * (a + b)", "a * a + 2 * a * b + b * b"),
    ("equiv", "a * b * c", "c * (b * a)"),
    ("equiv", "a * b / 100", "a / 100 * b"),
    ("always", "a <= 1000 && b <= 100 && a >= 0 && b >= 0 ? a * b <= 100000 : true", None),
    ("always", "b > 0 ? a * b / b == a : true", None),
    ("always", "a * a >= 0", None),
    ("always", "a <= b && c >= 0 ? a * c <= b * c : true", None),
    ("always", "a >= 0 && b >= 0 && c >= 0 && d >= 0 ? a * b + c * d >= 0 : true", None),
    ("always", "a * b % 7 == (a % 7) * (b % 7) % 7 || a < 0 || b < 0", None),
    ("sat", "a * b == 391 && a > 1 && b > 1", None),
    ("sat", "a * b == 1000003 && a > 1 && b > 1", None),
    ("can_error", "a * b * c * d", None),
]


def main() -> None:
    decided = total = 0
    times: list[float] = []
    for pname, t in PROFILES.items():
        env = Env(a=t, b=t, c=t, d=t)
        for kind, x, y in CASES:
            t0 = time.perf_counter()
            if kind == "equiv":
                v = env.expr(x, int).equivalent(env.expr(y or "", int), timeout=5.0)
            elif kind == "always":
                v = env.predicate(x).always_true(timeout=5.0)
            elif kind == "sat":
                v = env.predicate(x).satisfiable(timeout=5.0)
            else:
                v = env.expr(x, int).can_error(timeout=5.0)
            ms = (time.perf_counter() - t0) * 1000
            times.append(ms)
            total += 1
            decided += not v.unknown
            status = str(v.status).rsplit(".", 1)[-1]
            print(f"{pname:<6} {status:<8} {ms:8.1f} ms  {x}{' == ' + y if y else ''}", flush=True)
    times.sort()
    print(f"decided {decided}/{total}, median {times[len(times) // 2]:.1f} ms, max {times[-1]:.1f} ms")


if __name__ == "__main__":
    main()
