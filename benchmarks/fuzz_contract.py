"""Contract fuzzer: random in-subset expressions must be decided, quickly and correctly.

The contract: if an expression compiles, the verifier answers PROVED/REFUTED (SAT/UNSAT)
quickly. This generates type-directed expressions from the subset over a bounded schema,
asks every question about them, and reports

- UNKNOWN      a verdict that isn't decided (a contract bug: fix the encoding or drop the
               construct from the subset),
- WRONG        a decided verdict that random concrete inputs contradict (a soundness bug),
- SLOW         a decided verdict over the time budget,
- REJECTED     a generated expression that doesn't compile (a generator bug; reported only).

Failures are shrunk (subtrees replaced by leaves while the failure persists).

Run:
  uv run python benchmarks/fuzz_contract.py --count 300 --seed 1     # explore
  uv run python benchmarks/fuzz_contract.py --gate                    # the ratchet in check.sh
  uv run python benchmarks/fuzz_contract.py --gate --update           # accept the current set

The gate runs fixed seeds and fails on any WRONG verdict, and on any UNKNOWN not listed
in benchmarks/contract_known.txt. Listed failures are skipped (``--recheck`` retries them
and reports the ones that now pass, so the list only shrinks).
"""

from __future__ import annotations

import argparse
import random
import sys
import time
from dataclasses import dataclass
from pathlib import Path
from typing import TYPE_CHECKING, Annotated, Any

from pydantic import Field

from celspresso import CelError, CelEvaluationError, Env, Status

if TYPE_CHECKING:
    from collections.abc import Callable, Iterator

KNOWN = Path(__file__).with_name("contract_known.txt")

# -- schema -----------------------------------------------------------------

Small = Annotated[int, Field(ge=-20, le=20)]
Digit = Annotated[int, Field(ge=0, le=9)]
Short = Annotated[str, Field(max_length=6)]
Word = Annotated[str, Field(max_length=4)]
SCHEMA: dict[str, Any] = {
    "s": Short,
    "t": Short,
    "n": Annotated[int, Field(ge=0, le=99)],
    "k": Small,
    "m": Annotated[int, Field(ge=0, le=9999)],
    "b": bool,
    "xs": Annotated[list[Digit], Field(max_length=3)],
    "ws": Annotated[list[Word], Field(max_length=3)],
}
VARS = {"I": ["n", "k", "m"], "S": ["s", "t"], "B": ["b"], "LI": ["xs"], "LS": ["ws"]}
ALPHABET = "ab-A1 "
PATTERNS = ["^[a-z]+$", "^[0-9]{2}$", "^a", "b$", "^[A-Za-z ]*$", "^(ab)+$", "-"]


def random_input(rng: random.Random) -> dict[str, Any]:
    def text(n: int) -> str:
        return "".join(rng.choice(ALPHABET) for _ in range(rng.randint(0, n)))

    def pick(lo: int, hi: int) -> int:  # favor edges, where off-by-ones live
        return rng.choice([lo, hi, 0 if lo <= 0 <= hi else lo, rng.randint(lo, hi), rng.randint(lo, hi)])

    return {
        "s": text(6),
        "t": text(6),
        "n": pick(0, 99),
        "k": pick(-20, 20),
        "m": pick(0, 9999),
        "b": rng.random() < 0.5,
        "xs": [rng.randint(0, 9) for _ in range(rng.randint(0, 3))],
        "ws": [text(4) for _ in range(rng.randint(0, 3))],
    }


# -- expression trees ---------------------------------------------------------


@dataclass(frozen=True)
class Node:
    """A typed expression: `fmt` with `{0}`, `{1}`, ... filled by the children's text."""

    ty: str
    fmt: str
    kids: tuple[Node, ...] = ()

    def text(self) -> str:
        return self.fmt.format(*(k.text() for k in self.kids))

    def size(self) -> int:
        return 1 + sum(k.size() for k in self.kids)


def leaf(ty: str, text: str) -> Node:
    return Node(ty, text.replace("{", "{{").replace("}", "}}"))


def str_lit(rng: random.Random) -> str:
    return "'" + "".join(rng.choice(ALPHABET) for _ in range(rng.randint(0, 3))) + "'"


class Gen:
    def __init__(self, rng: random.Random) -> None:
        self.rng = rng
        self.scope: dict[str, list[str]] = {}  # comprehension variables in scope, by type
        self.fresh = 0

    def var(self, ty: str) -> Node:
        names = VARS[ty] + self.scope.get(ty, [])
        return leaf(ty, self.rng.choice(names))

    def lit(self, ty: str) -> Node:
        r = self.rng
        return {
            "I": lambda: leaf("I", str(r.choice([0, 1, 2, 3, 7, 10, 100, -1, -5]))),
            "S": lambda: leaf("S", str_lit(r)),
            "B": lambda: leaf("B", r.choice(["true", "false"])),
            "LI": lambda: leaf(
                "LI", "[" + ", ".join(str(r.randint(0, 9)) for _ in range(r.randint(0, 2))) + "]"
            ),
            "LS": lambda: leaf("LS", "[" + ", ".join(str_lit(r) for _ in range(r.randint(0, 2))) + "]"),
        }[ty]()

    def leaf(self, ty: str) -> Node:
        return self.var(ty) if self.rng.random() < 0.7 else self.lit(ty)

    def bind(self, ty: str, body: Callable[[str], Node]) -> Node:
        self.fresh += 1
        name = f"v{self.fresh}"
        self.scope.setdefault(ty, []).append(name)
        try:
            return body(name)
        finally:
            self.scope[ty].remove(name)

    def gen(self, ty: str, depth: int) -> Node:
        if depth <= 0 or self.rng.random() < 0.2:
            return self.leaf(ty)
        options = getattr(self, f"g_{ty}")(depth - 1)
        return self.rng.choice(options)()

    # each g_* returns thunks, so only the chosen branch is built
    def g_I(self, d: int) -> list[Callable[[], Node]]:
        g, r = self.gen, self.rng
        nz = lambda: leaf("I", str(r.choice([1, 2, 3, 7, 10, -3])))  # noqa: E731
        return [
            lambda: Node("I", "({0} + {1})", (g("I", d), g("I", d))),
            lambda: Node("I", "({0} - {1})", (g("I", d), g("I", d))),
            lambda: Node("I", "({0} * {1})", (g("I", d), self.lit("I"))),
            lambda: Node("I", "({0} * {1})", (self.var("I"), self.var("I"))),
            lambda: Node("I", "({0} / {1})", (g("I", d), nz())),
            lambda: Node("I", "({0} % {1})", (g("I", d), nz())),
            lambda: Node("I", "-({0})", (g("I", d),)),
            lambda: Node("I", "({0} ? {1} : {2})", (g("B", d), g("I", d), g("I", d))),
            lambda: Node("I", "size({0})", (g("S", d),)),
            lambda: Node("I", "size({0})", (g("LI", d),)),
            lambda: Node("I", "{0}.indexOf({1})", (g("S", d), leaf("S", str_lit(r)))),
            lambda: Node("I", "math.greatest({0}, {1})", (g("I", d), g("I", d))),
            lambda: Node("I", "math.least({0}, {1})", (g("I", d), g("I", d))),
            lambda: Node("I", "{0}.sum()", (g("LI", d),)),
            lambda: Node("I", "int({0})", (Node("S", "string({0})", (g("I", d),)),)),
        ]

    def g_S(self, d: int) -> list[Callable[[], Node]]:
        g, r = self.gen, self.rng
        return [
            lambda: Node("S", "({0} + {1})", (g("S", d), g("S", d))),
            lambda: Node("S", "string({0})", (g("I", d),)),
            lambda: Node("S", "{0}.lowerAscii()", (g("S", d),)),
            lambda: Node("S", "{0}.upperAscii()", (g("S", d),)),
            lambda: Node("S", "({0} ? {1} : {2})", (g("B", d), g("S", d), g("S", d))),
            lambda: Node("S", "{0}.join({1})", (g("LS", d), leaf("S", str_lit(r)))),
            lambda: Node("S", "{0}.substring({1})", (g("S", d), leaf("I", str(r.randint(0, 3))))),
        ]

    def g_B(self, d: int) -> list[Callable[[], Node]]:
        g, r = self.gen, self.rng
        cmp = lambda: r.choice(["==", "!=", "<", "<=", ">", ">="])  # noqa: E731
        return [
            lambda: Node("B", "({0} " + cmp() + " {1})", (g("I", d), g("I", d))),
            lambda: Node("B", "({0} " + r.choice(["==", "!="]) + " {1})", (g("S", d), g("S", d))),
            lambda: Node("B", "{0}.startsWith({1})", (g("S", d), g("S", d))),
            lambda: Node("B", "{0}.endsWith({1})", (g("S", d), leaf("S", str_lit(r)))),
            lambda: Node("B", "{0}.contains({1})", (g("S", d), leaf("S", str_lit(r)))),
            lambda: Node(
                "B",
                "{0}.matches('" + r.choice(PATTERNS).replace("{", "{{").replace("}", "}}") + "')",
                (g("S", d),),
            ),
            lambda: Node("B", "({0} in {1})", (g("I", d), g("LI", d))),
            lambda: Node("B", "({0} in {1})", (g("S", d), g("LS", d))),
            lambda: Node("B", "!({0})", (g("B", d),)),
            lambda: Node("B", "({0} && {1})", (g("B", d), g("B", d))),
            lambda: Node("B", "({0} || {1})", (g("B", d), g("B", d))),
            lambda: self.bind(
                "I",
                lambda v: Node(
                    "B", "{0}." + r.choice(["exists", "all"]) + f"({v}, {{1}})", (self.var("LI"), g("B", d))
                ),
            ),
            lambda: self.bind(
                "S", lambda v: Node("B", "{0}.exists(" + v + ", {1})", (self.var("LS"), g("B", d)))
            ),
        ]

    def g_LI(self, d: int) -> list[Callable[[], Node]]:
        g = self.gen
        return [
            lambda: Node("LI", "({0} + {1})", (g("LI", d), self.lit("LI"))),
            lambda: self.bind(
                "I", lambda v: Node("LI", "{0}.filter(" + v + ", {1})", (self.var("LI"), g("B", d)))
            ),
            lambda: self.bind(
                "I", lambda v: Node("LI", "{0}.map(" + v + ", {1})", (self.var("LI"), g("I", d)))
            ),
        ]

    def g_LS(self, d: int) -> list[Callable[[], Node]]:
        g, r = self.gen, self.rng
        return [
            lambda: Node("LS", "{0}.split({1})", (g("S", d), leaf("S", r.choice(["'-'", "' '", "'a'"])))),
            lambda: self.bind(
                "S", lambda v: Node("LS", "{0}.map(" + v + ", {1})", (self.var("LS"), g("S", d)))
            ),
            lambda: Node("LS", "({0} + {1})", (g("LS", d), self.lit("LS"))),
        ]


# -- questions and soundness checks ---------------------------------------------


@dataclass
class Outcome:
    question: str
    source: str
    status: str  # PROVED/REFUTED/SAT/UNSAT, UNKNOWN, WRONG, REJECTED
    ms: float
    detail: str = ""

    @property
    def key(self) -> str:
        return f"{self.question}\t{self.source}"


def run_value(env: Env, src: str, data: dict[str, Any]) -> tuple[bool, Any]:
    """(ok, value-or-None): ok is False when evaluation raises a CEL error."""
    try:
        return True, env.compile(src).evaluate(data)
    except CelEvaluationError:
        return False, None


def ask(env: Env, question: str, node: Node, other: Node | None, timeout: float) -> Outcome:
    src = node.text()
    shown = src if other is None else f"{src}  <=>  {other.text()}"
    t0 = time.perf_counter()
    try:
        if question == "always_true":
            v = env.predicate(src).always_true(timeout=timeout)
        elif question == "satisfiable":
            v = env.predicate(src).satisfiable(timeout=timeout)
        elif question == "can_error":
            v = env.compile(src).can_error(timeout=timeout)
        else:
            assert other is not None
            py = {"I": int, "S": str, "B": bool, "LI": list[int], "LS": list[str]}[node.ty]
            v = env.expr(src, py).equivalent(env.expr(other.text(), py), timeout=timeout)
    except CelError as e:
        return Outcome(question, shown, "REJECTED", 0.0, str(e).splitlines()[1] if "\n" in str(e) else str(e))
    ms = (time.perf_counter() - t0) * 1000
    status = v.status.name
    return Outcome(question, shown, status, ms, (v.reason or "") if v.status is Status.UNKNOWN else "")


def contradicted(
    env: Env, out: Outcome, node: Node, other: Node | None, rng: random.Random, samples: int
) -> str:
    """A concrete input that contradicts a decided verdict, if sampling finds one."""
    src = node.text()
    for _ in range(samples):
        data = random_input(rng)
        ok, val = run_value(env, src, data)
        if out.question == "always_true" and out.status == "PROVED" and not (ok and val is True):
            return f"PROVED but {data} gives {'an error' if not ok else val!r}"
        if out.question == "satisfiable" and out.status == "UNSAT" and ok and val is True:
            return f"UNSAT but {data} satisfies it"
        if out.question == "can_error" and out.status == "UNSAT" and not ok:
            return f"can't error, but {data} errors"
        if out.question == "equivalent" and out.status == "PROVED":
            assert other is not None
            ok2, val2 = run_value(env, other.text(), data)
            if (ok, val) != (ok2, val2):
                return f"PROVED equivalent but {data} gives {val!r} vs {val2!r}"
    return ""


QUESTIONS = {"B": ["always_true", "satisfiable", "can_error"], "*": ["can_error", "equivalent"]}


def mutate(g: Gen, node: Node, depth: int) -> Node:
    """A variant for equivalence: a meaning-preserving rewrite half the time, else a random edit."""
    r = g.rng
    if r.random() < 0.5:
        swaps = {
            "({0} + {1})": "({1} + {0})",
            "({0} * {1})": "({1} * {0})",
            "({0} && {1})": "({1} && {0})",
            "({0} || {1})": "({1} || {0})",
        }

        def rewrite(n: Node) -> Node:
            kids = tuple(rewrite(k) for k in n.kids)
            if n.fmt in swaps and n.ty in ("I", "B") and r.random() < 0.7:
                return Node(n.ty, swaps[n.fmt], kids)
            if n.fmt.startswith("({0} ? ") and r.random() < 0.5:  # c ? a : b  ==  !c ? b : a
                return Node(n.ty, "(!({0}) ? {2} : {1})", kids)
            return Node(n.ty, n.fmt, kids)

        return rewrite(node)
    # replace one random subtree of the same type
    subs = list(walk(node))
    target = r.choice(subs)
    repl = g.gen(target.ty, max(1, depth - 1))
    return replace(node, target, repl)


def walk(n: Node) -> Iterator[Node]:
    yield n
    for k in n.kids:
        yield from walk(k)


def replace(n: Node, target: Node, repl: Node) -> Node:
    if n is target:
        return repl
    return Node(n.ty, n.fmt, tuple(replace(k, target, repl) for k in n.kids))


def shrink(
    env: Env, out: Outcome, node: Node, other: Node | None, g: Gen, timeout: float
) -> tuple[Node, Node | None]:
    """Replace subtrees with leaves while the failure persists (UNKNOWN stays UNKNOWN)."""
    if out.status != "UNKNOWN" or other is not None:  # pairs are kept whole
        return node, other
    improved = True
    while improved:
        improved = False
        for target in sorted(walk(node), key=lambda n: -n.size()):
            if not target.kids:
                continue
            for cand in (g.var(target.ty), g.lit(target.ty)):
                smaller = replace(node, target, cand)
                if ask(env, out.question, smaller, None, timeout).status == "UNKNOWN":
                    node, improved = smaller, True
                    break
            if improved:
                break
    return node, other


# -- driver -------------------------------------------------------------------


def fuzz(
    seed: int,
    count: int,
    timeout: float,
    budget_ms: float,
    samples: int,
    known: set[str],
    skip_known: bool,
    *,
    gate: bool = False,
    depth: int = 3,
) -> list[Outcome]:
    """Ask every question of `count` random expressions. Each expression draws from its own
    generator, so a verdict that changes (a timeout near the limit) never changes the rest.
    In gate mode a timeout is retried at 4x the limit before it counts as UNKNOWN, and
    nothing is shrunk: outcomes are keyed by the generated source, never a timing-dependent
    shrink."""
    env = Env(**SCHEMA)
    outs: list[Outcome] = []
    for i in range(count):
        rng = random.Random(seed * 1_000_003 + i)
        g = Gen(rng)
        ty = rng.choice(["B", "B", "B", "I", "S", "LI"])
        node = g.gen(ty, depth)
        for q in QUESTIONS["B"] if ty == "B" else QUESTIONS["*"]:
            other = mutate(g, node, depth) if q == "equivalent" else None
            key_src = node.text() if other is None else f"{node.text()}  <=>  {other.text()}"
            if skip_known and f"{q}\t{key_src}" in known:
                continue
            out = ask(env, q, node, other, timeout)
            if gate and out.status == "UNKNOWN" and "timeout" in out.detail:
                out = ask(env, q, node, other, timeout * 4)
                if out.status != "UNKNOWN":
                    out.detail = "SLOW"  # decided, but only with the longer limit
            if out.status in ("PROVED", "REFUTED", "SAT", "UNSAT"):
                bad = contradicted(env, out, node, other, rng, samples)
                if bad:
                    out.status, out.detail = "WRONG", bad
                elif out.ms > budget_ms:
                    out.detail = "SLOW"
            elif out.status == "UNKNOWN" and not gate:
                n2, o2 = shrink(env, out, node, other, g, timeout)
                if n2 is not node:
                    out = Outcome(
                        q,
                        n2.text() if o2 is None else f"{n2.text()}  <=>  {o2.text()}",
                        "UNKNOWN",
                        out.ms,
                        out.detail + f"  (shrunk from: {key_src})",
                    )
            outs.append(out)
    return outs


def report(outs: list[Outcome]) -> None:
    decided = [o for o in outs if o.status in ("PROVED", "REFUTED", "SAT", "UNSAT")]
    times = sorted(o.ms for o in decided) or [0.0]
    by = lambda s: [o for o in outs if o.status == s]  # noqa: E731
    slow = [o for o in decided if o.detail == "SLOW"]
    print(
        f"{len(outs)} questions: {len(decided)} decided, {len(by('UNKNOWN'))} UNKNOWN, {len(by('WRONG'))} WRONG, "
        f"{len(slow)} slow, {len(by('REJECTED'))} rejected by the subset; "
        f"decided median {times[len(times) // 2]:.0f} ms, p99 {times[int(len(times) * 0.99)]:.0f} ms, max {times[-1]:.0f} ms"
    )
    for label, group in [
        ("WRONG", by("WRONG")),
        ("UNKNOWN", by("UNKNOWN")),
        ("SLOW", slow),
        ("REJECTED", by("REJECTED")),
    ]:
        for o in group[:25]:
            print(f"  {label:<8} {o.ms:7.0f} ms  {o.question:<11} {o.source}\n{'':12}{o.detail}"[:600])


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--count", type=int, default=200, help="expressions per seed")
    ap.add_argument("--timeout", type=float, default=3.0, help="solver timeout per question (s)")
    ap.add_argument(
        "--budget", type=float, default=1000.0, help="report decided questions slower than this (ms)"
    )
    ap.add_argument("--samples", type=int, default=40, help="random inputs per decided verdict")
    ap.add_argument(
        "--gate", action="store_true", help="fixed seeds (3 x 40); fail on WRONG or a new UNKNOWN"
    )
    ap.add_argument("--update", action="store_true", help="with --gate: write the current UNKNOWNs as known")
    ap.add_argument("--recheck", action="store_true", help="with --gate: retry known failures too")
    a = ap.parse_args(argv)
    known = set(KNOWN.read_text().splitlines()) - {""} if KNOWN.exists() else set()
    known = {k for k in known if not k.startswith("#")}
    if not a.gate:
        report(fuzz(a.seed, a.count, a.timeout, a.budget, a.samples, known, skip_known=False))
        return 0
    outs = [
        o
        for seed in (1, 2, 3)
        for o in fuzz(
            seed, 40, a.timeout, a.budget, a.samples, known, skip_known=not (a.recheck or a.update), gate=True
        )
    ]
    report(outs)
    unknown = {o.key for o in outs if o.status == "UNKNOWN"}
    wrong = [o for o in outs if o.status == "WRONG"]
    if a.update:
        KNOWN.write_text(
            "# Contract fuzzer: in-subset questions that are still UNKNOWN (see benchmarks/fuzz_contract.py).\n"
            "# Each is a contract bug to fix; the gate fails on any UNKNOWN not listed here.\n"
            + "".join(f"{k}\n" for k in sorted(unknown))
        )
        print(f"wrote {len(unknown)} known UNKNOWNs to {KNOWN.name}")
        return 1 if wrong else 0
    if a.recheck:
        fixed = sorted(known - unknown)
        print(f"{len(fixed)} known failures now decided" + "".join(f"\n  fixed: {k}" for k in fixed))
    new = sorted(unknown - known)
    for k in new:
        print(f"NEW UNKNOWN: {k}")
    if wrong or new:
        print("contract gate FAILED")
        return 1
    print(f"contract gate ok ({len(known)} known UNKNOWNs)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
