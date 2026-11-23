"""String-expression equivalence benchmark: pairs of rewrites, equivalent or not.

Run:  uv run maturin develop --release && uv run python benchmarks/bench_strings.py [--runs N]

Each case states what the answer should be. A case whose verdict differs (other than
an UNKNOWN on a case marked hard) is flagged, so the corpus doubles as a check.
"""

from __future__ import annotations

import argparse
import statistics
import time
from typing import Annotated

from pydantic import Field

from celspresso import Env

Name = Annotated[str, Field(max_length=30)]
ENV = Env(
    first=Name,
    last=Name,
    code=Annotated[str, Field(max_length=10)],
    n=Annotated[int, Field(ge=0, le=99999)],
    amount=Annotated[int, Field(ge=0, le=10_000_000)],
    flag=bool,
    xs=Annotated[list[Name], Field(max_length=4)],
)

PAD2 = "(amount % 100 < 10 ? '0' : '') + string(amount % 100)"

# (name, a, b, expected: True = equivalent, False = not, None = hard: UNKNOWN accepted)
CASES: list[tuple[str, str, str, bool | None]] = [
    ("identical", "first + ' ' + last", "first + ' ' + last", True),
    ("concat vs join", "first + ' ' + last", "[first, last].join(' ')", True),
    ("size of concat", "size(first + last)", "size(first) + size(last)", True),
    ("ternary flipped", "flag ? 'Y' : 'N'", "!flag ? 'N' : 'Y'", True),
    ("pad flipped", "n > 9 ? string(n) : '0' + string(n)", "n < 10 ? '0' + string(n) : string(n)", True),
    ("pad off by one", "n > 9 ? string(n) : '0' + string(n)", "n >= 9 ? string(n) : '0' + string(n)", False),
    ("contains vs indexOf", "first.contains(' ')", "first.indexOf(' ') >= 0", True),
    ("bounded by schema", "first.startsWith('A') && size(first) <= 30", "first.startsWith('A')", True),
    ("regex split", "code.matches('^[0-9]{5}$')", "size(code) == 5 && code.matches('^[0-9]+$')", True),
    (
        "cents two ways",
        f"string(amount / 100) + '.' + {PAD2}",
        "string(amount / 100) + '.' + string(amount % 100 / 10) + string(amount % 10)",
        True,
    ),
    (
        "cents unpadded",
        f"string(amount / 100) + '.' + {PAD2}",
        "string(amount / 100) + '.' + string(amount % 100)",
        False,
    ),
    ("concat order", "first + last", "last + first", False),
    (
        "skip empty",
        "first == '' ? last : first + ' ' + last",
        "[first, last].filter(x, x != '').join(' ')",
        False,
    ),
    ("case of concat", "first.upperAscii() + last.upperAscii()", "(first + last).upperAscii()", None),
    ("split vs contains", "first.split(' ').size() > 1", "first.contains(' ')", None),
    ("int round trip", "int(string(n))", "n", True),
    ("join filter", "xs.filter(x, x != '').join(',')", "xs.filter(x, size(x) > 0).join(',')", True),
]


def run(runs: int) -> None:
    print(f"| {'case':<22} | {'expect':<6} | {'status':<8} | {'median ms':>9} | {'max ms':>8} |")
    print(f"|{'-' * 24}|{'-' * 8}|{'-' * 10}|{'-' * 11}|{'-' * 10}|")
    walls_all: list[float] = []
    bad = 0
    for name, a, b, expect in CASES:
        ea, eb = ENV.compile(a), ENV.compile(b)
        walls: list[float] = []
        status = ""
        for _ in range(runs):
            t0 = time.perf_counter()
            v = ea.equivalent(eb)
            walls.append((time.perf_counter() - t0) * 1000)
            status = v.status.name
        walls_all.extend(walls)
        want = {True: "PROVED", False: "REFUTED", None: "PROVED"}[expect]
        ok = status == want or (expect is None and status == "UNKNOWN")
        bad += not ok
        flag = "" if ok else "  <-- unexpected"
        tag = {True: "equiv", False: "differ", None: "hard"}[expect]
        print(
            f"| {name:<22} | {tag:<6} | {status:<8} | {statistics.median(walls):>9.2f} | {max(walls):>8.2f} |{flag}"
        )
    walls_all.sort()
    print(
        f"\nall: median {statistics.median(walls_all):.2f} ms, "
        f"p95 {walls_all[int(len(walls_all) * 0.95)]:.2f} ms, max {walls_all[-1]:.2f} ms, unexpected {bad}"
    )


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--runs", type=int, default=5)
    run(ap.parse_args().runs)
