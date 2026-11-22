from __future__ import annotations

import inspect
import typing
from collections.abc import Callable, Iterable, Mapping
from dataclasses import dataclass
from typing import Any, Generic, Literal, TypeVar, overload

from . import _celspresso as _core
from ._errors import CelEvaluationError, CelSyntaxError, CelTypeError, Diagnostic
from ._types import SchemaBuilder, TypeSpec, cel_literal, from_cel, type_name
from ._verdict import Stats, Status, Verdict, Witness

__all__ = ["Env", "Explanation", "Expr", "Predicate", "function"]

T = TypeVar("T")
ErrorMode = Literal["strict", "as_false"]
Assumption = "str | Predicate"

_RESERVED = {"timeout", "unroll_limit", "schema_constraints"}


def _raise_compile(source: str, exc: Exception) -> typing.NoReturn:
    kind, items = exc.args
    diags = [Diagnostic(m, a, b, r) for (m, a, b, r) in items]
    cls = CelSyntaxError if kind == "syntax" else CelTypeError
    raise cls(source, diags) from None


def function(fn: Callable[..., Any] | None = None, *, name: str | None = None) -> Any:
    """Mark a Python callable as a CEL function (optionally renaming it).

    Pass the result to `Env.extend(functions=[...])`. Parameter and return types
    come from the type hints. The verifier treats custom functions as
    uninterpreted: it knows they are deterministic, nothing more.
    """

    def wrap(f: Callable[..., Any]) -> Callable[..., Any]:
        f.__cel_name__ = name or f.__name__  # type: ignore[attr-defined]
        return f

    return wrap(fn) if fn is not None else wrap


@dataclass(frozen=True)
class _Fn:
    name: str
    impl: Callable[..., Any]
    params: tuple[TypeSpec, ...]
    result: TypeSpec


class Env:
    """An immutable CEL environment: variables, types, functions, definitions.

    >>> env = Env(x=int, name=str)
    >>> env.predicate("x > 3 && name.startsWith('a')").evaluate({"x": 5, "name": "ab"})
    True
    """

    def __init__(
        self,
        *,
        timeout: float = 5.0,
        unroll_limit: int = 5,
        schema_constraints: bool = True,
        **variables: Any,
    ) -> None:
        self._timeout = timeout
        self._unroll = unroll_limit
        self._schema_constraints = schema_constraints
        self._builder = SchemaBuilder()
        self._vars: dict[str, tuple[TypeSpec, dict[str, Any] | None]] = {}
        self._fns: dict[str, _Fn] = {}
        self._defs: tuple[tuple[str, str], ...] = ()
        self._assumptions: tuple[str, ...] = ()
        for n, tp in variables.items():
            self._vars[n] = self._builder.convert(tp, n)
        self._build()

    # -- construction -----------------------------------------------------

    def _clone(self) -> Env:
        e = object.__new__(Env)
        e._timeout = self._timeout
        e._unroll = self._unroll
        e._schema_constraints = self._schema_constraints
        e._builder = self._builder.copy()
        e._vars = dict(self._vars)
        e._fns = dict(self._fns)
        e._defs = self._defs
        e._assumptions = self._assumptions
        return e

    def _build(self) -> None:
        structs = [(n, fields) for n, fields in self._builder.structs.items()]
        variables = [(n, spec, cons) for n, (spec, cons) in self._vars.items()]
        fns = [
            (f.name, f"{f.name}_{len(f.params)}", False, list(f.params), f.result) for f in self._fns.values()
        ]
        try:
            self._core = _core.Core(structs, variables, fns, list(self._defs))
        except _core.CompileError as exc:
            # a definition failed to compile
            _raise_compile(self._defs[-1][1] if self._defs else "", exc)
        self._fn_impls = {f.name: f.impl for f in self._fns.values()}
        self._fingerprint = (
            tuple(sorted((n, repr(s)) for n, s in self._vars.items())),
            tuple(sorted(self._fns)),
            self._defs,
        )

    def extend(
        self,
        *,
        functions: Iterable[Callable[..., Any]] = (),
        assumptions: Iterable[str | Predicate] = (),
        timeout: float | None = None,
        unroll_limit: int | None = None,
        **variables: Any,
    ) -> Env:
        """Return a new Env with more variables, functions, or standing assumptions."""
        e = self._clone()
        for n, tp in variables.items():
            if n in e._vars:
                raise ValueError(f"variable '{n}' is already declared")
            e._vars[n] = e._builder.convert(tp, n)
        for f in functions:
            fn = _function_decl(f, e._builder)
            e._fns[fn.name] = fn
        if timeout is not None:
            e._timeout = timeout
        if unroll_limit is not None:
            e._unroll = unroll_limit
        e._build()
        new_asm = [a if isinstance(a, str) else a.source for a in assumptions]
        for a in new_asm:
            e.predicate(a)  # validate now
        e._assumptions = self._assumptions + tuple(new_asm)
        return e

    def define(self, name: str, source: str) -> Env:
        """Return a new Env where `name` is a reusable named sub-expression."""
        if not name.isidentifier():
            raise ValueError(f"invalid definition name {name!r}")
        self.compile(source)  # type-check against the current env first
        e = self._clone()
        e._defs = self._defs + ((name, source),)
        e._build()
        return e

    def table(self, name: str, data: Iterable[Any] | Mapping[Any, Any]) -> Env:
        """Return a new Env with a constant lookup table (a set/list or a mapping)."""
        if isinstance(data, Mapping):
            return self.define(name, cel_literal(dict(data)))
        return self.define(name, cel_literal(sorted(set(data), key=repr)))

    # -- compilation ------------------------------------------------------

    def compile(self, source: str) -> Expr[Any]:
        """Compile CEL; returns a `Predicate` for bool expressions, `Expr` otherwise."""
        try:
            prog = self._core.compile(source)
        except _core.CompileError as exc:
            _raise_compile(source, exc)
        if prog.output_type == "bool":
            return Predicate(self, prog)
        return Expr(self, prog)

    def predicate(self, source: str) -> Predicate:
        """Compile a boolean expression; raises CelTypeError for any other type."""
        e = self.compile(source)
        if not isinstance(e, Predicate):
            _type_mismatch(source, e, "bool")
        return e

    @overload
    def expr(self, source: str) -> Expr[Any]: ...
    @overload
    def expr(self, source: str, type: type[T]) -> Expr[T]: ...
    def expr(self, source: str, type: Any = None) -> Expr[Any]:
        """Compile an expression, optionally asserting its result type."""
        e = self.compile(source)
        if type is not None:
            want, _ = self._builder.copy().convert(type, "expected type")
            got = e._prog.output_type
            if got != "dyn" and got != want:
                _type_mismatch(source, e, type_name(want))
            if want == "bool" and not isinstance(e, Predicate):
                e = Predicate(self, e._prog)
        return e

    # -- introspection ----------------------------------------------------

    @property
    def variables(self) -> dict[str, str]:
        return {n: type_name(s) for n, (s, _) in self._vars.items()}

    @property
    def assumptions(self) -> tuple[str, ...]:
        return self._assumptions

    def __repr__(self) -> str:
        vs = ", ".join(f"{n}: {t}" for n, t in self.variables.items())
        return f"Env({vs})"

    # -- internals used by Expr --------------------------------------------

    def _specs(self) -> dict[str, TypeSpec]:
        return {n: s for n, (s, _) in self._vars.items()}

    def _verify(
        self,
        kind: str,
        question: str,
        a: Expr[Any],
        b: Expr[Any] | None,
        assuming: Iterable[str | Predicate] | str | Predicate,
        timeout: float | None,
        errors: ErrorMode = "strict",
        found: Status = Status.SAT,
        not_found: Status = Status.UNSAT,
    ) -> Verdict:
        for x in (a, b):
            if x is not None and x._env._fingerprint != self._fingerprint:
                raise ValueError("expressions come from different environments")
        if isinstance(assuming, (str, Predicate)):
            assuming = [assuming]
        asm_src = list(self._assumptions) + [x if isinstance(x, str) else x.source for x in assuming]
        asm = [self.predicate(s)._prog for s in asm_src]
        out = _core.verify(
            kind,
            a._prog,
            b._prog if b is not None else None,
            asm,
            int((timeout if timeout is not None else self._timeout) * 1000),
            self._unroll,
            self._schema_constraints,
            errors,
            self._fn_impls,
        )
        stats = Stats(out["elapsed_ms"], tuple(out["approximations"]))
        common = {
            "question": question,
            "bounded": out["bounded"],
            "assumptions": tuple(asm_src),
            "stats": stats,
        }
        if out["status"] == "found":
            w = Witness(out["witness"], self._specs(), self._builder.classes)
            try:
                w.to_python()
            except Exception as exc:  # noqa: BLE001 - any validator failure means the witness is not real
                return Verdict(
                    Status.UNKNOWN,
                    reason=f"solver witness fails model validation ({type(exc).__name__}); "
                    "the expression may depend on validators the verifier does not model",
                    **common,  # type: ignore[arg-type]
                )
            return Verdict(found, witness=w, **common)  # type: ignore[arg-type]
        if out["status"] == "not_found":
            return Verdict(not_found, **common)  # type: ignore[arg-type]
        return Verdict(Status.UNKNOWN, reason=out["reason"], **common)  # type: ignore[arg-type]


def _type_mismatch(source: str, e: Expr[Any], want: str) -> typing.NoReturn:
    msg = f"expression has type {e.output_type}, expected {want}"
    raise CelTypeError(source, [Diagnostic(msg, 0, len(source), f"{msg}\n  | {source}")])


def _function_decl(f: Callable[..., Any], builder: SchemaBuilder) -> _Fn:
    name = getattr(f, "__cel_name__", None) or f.__name__
    hints = typing.get_type_hints(f, include_extras=True)
    sig = inspect.signature(f)
    params = []
    for p in sig.parameters.values():
        if p.name not in hints:
            raise TypeError(f"function '{name}': parameter '{p.name}' needs a type hint")
        params.append(builder.convert(hints[p.name], f"{name}({p.name})")[0])
    if "return" not in hints:
        raise TypeError(f"function '{name}' needs a return type hint")
    return _Fn(name, f, tuple(params), builder.convert(hints["return"], f"{name} result")[0])


def _operand(env: Env, x: Any) -> str:
    if isinstance(x, Expr):
        if x._env._fingerprint != env._fingerprint:
            raise ValueError("expressions come from different environments")
        return f"({x.source})"
    return cel_literal(x)


class Expr(Generic[T]):
    """A compiled, type-checked CEL expression producing a `T`."""

    __slots__ = ("_env", "_prog")

    def __init__(self, env: Env, prog: Any) -> None:
        self._env = env
        self._prog = prog

    # -- metadata ---------------------------------------------------------

    @property
    def source(self) -> str:
        return self._prog.source

    @property
    def canonical(self) -> str:
        """Normalized CEL text (definitions expanded)."""
        return self._prog.canonical

    @property
    def output_type(self) -> str:
        return self._prog.output_type_name

    @property
    def references(self) -> list[str]:
        """Variables and field paths this expression reads, e.g. ['user.age']."""
        return self._prog.references

    @property
    def env(self) -> Env:
        return self._env

    def __repr__(self) -> str:
        return f"{type(self).__name__}({self.source!r}, type={self.output_type})"

    def __hash__(self) -> int:
        return hash((self._env._fingerprint, self.canonical))

    def __eq__(self, other: object) -> bool:
        raise TypeError(
            "use .equivalent() to compare meaning, .eq() to build a CEL comparison, "
            "or .same_as() for syntactic identity"
        )

    def same_as(self, other: Expr[Any]) -> bool:
        """Syntactic identity (same env, same canonical text)."""
        return self._env._fingerprint == other._env._fingerprint and self.canonical == other.canonical

    # -- evaluation -------------------------------------------------------

    def evaluate(self, data: Mapping[str, Any] | None = None) -> T:
        """Evaluate against a mapping of variable values (models, dicts, scalars)."""
        try:
            raw = self._prog.evaluate(dict(data or {}), self._env._fn_impls)
        except _core.EvalError as exc:
            msg, eid, a, b, rendered = exc.args
            raise CelEvaluationError(msg, eid, (a, b), rendered) from None
        return from_cel(raw, self._prog.output_type, self._env._builder.classes)

    def explain(self, data: Mapping[str, Any] | None = None) -> Explanation:
        """Evaluate and record the value of every sub-expression."""
        ok, value, nodes = self._prog.explain(dict(data or {}), self._env._fn_impls)
        return Explanation(self.source, ok, value, [(a, b, k, v) for (a, b, k, v) in nodes])

    # -- comparisons that build predicates --------------------------------

    def _cmp(self, op: str, other: Any) -> Predicate:
        return self._env.predicate(f"({self.source}) {op} {_operand(self._env, other)}")

    def eq(self, other: Any) -> Predicate:
        return self._cmp("==", other)

    def ne(self, other: Any) -> Predicate:
        return self._cmp("!=", other)

    def lt(self, other: Any) -> Predicate:
        return self._cmp("<", other)

    def le(self, other: Any) -> Predicate:
        return self._cmp("<=", other)

    def gt(self, other: Any) -> Predicate:
        return self._cmp(">", other)

    def ge(self, other: Any) -> Predicate:
        return self._cmp(">=", other)

    def in_(self, container: Any) -> Predicate:
        return self._env.predicate(f"({self.source}) in {_operand(self._env, container)}")

    # -- verification -----------------------------------------------------

    def equivalent(
        self,
        other: Expr[Any] | str,
        *,
        errors: ErrorMode = "strict",
        assuming: Iterable[str | Predicate] | str | Predicate = (),
        timeout: float | None = None,
    ) -> Verdict:
        """PROVED if both expressions agree on every input (errors included, unless
        `errors="as_false"`); REFUTED with a counterexample otherwise."""
        o = self._env.compile(other) if isinstance(other, str) else other
        if errors == "as_false" and not (isinstance(self, Predicate) and isinstance(o, Predicate)):
            raise TypeError('errors="as_false" only applies to predicates')
        return self._env._verify(
            "equivalent",
            f"{self.source}  ≡  {o.source}",
            self,
            o,
            assuming,
            timeout,
            errors,
            found=Status.REFUTED,
            not_found=Status.PROVED,
        )

    def can_error(
        self, *, assuming: Iterable[str | Predicate] | str | Predicate = (), timeout: float | None = None
    ) -> Verdict:
        """SAT (with a witness) if some valid input makes evaluation fail."""
        return self._env._verify("can_error", f"can error: {self.source}", self, None, assuming, timeout)

    def can_equal(
        self,
        value: Any,
        *,
        assuming: Iterable[str | Predicate] | str | Predicate = (),
        timeout: float | None = None,
    ) -> Verdict:
        """SAT if some valid input makes the expression equal `value`."""
        return self.eq(value).satisfiable(assuming=assuming, timeout=timeout)

    def diff(self, other: Expr[Any], *, limit: int = 5, timeout: float | None = None) -> list[Witness]:
        """Up to `limit` distinct inputs on which the two expressions disagree."""
        found: list[Witness] = []
        blockers: list[str] = []
        paths = sorted(set(self.references) | set(other.references))
        while len(found) < limit:
            v = self.equivalent(other, assuming=blockers, timeout=timeout)
            if not v.refuted or v.witness is None:
                break
            found.append(v.witness)
            clause = _blocking_clause(v.witness, paths)
            if clause is None:
                break
            blockers.append(clause)
        return found


class Predicate(Expr[bool]):
    """A boolean expression: adds satisfiability, validity, implication and `& | ~`."""

    __slots__ = ()

    def satisfiable(
        self, *, assuming: Iterable[str | Predicate] | str | Predicate = (), timeout: float | None = None
    ) -> Verdict:
        """SAT with a witness if some valid input makes this true; UNSAT if none can."""
        return self._env._verify("satisfiable", f"satisfiable: {self.source}", self, None, assuming, timeout)

    def always_true(
        self, *, assuming: Iterable[str | Predicate] | str | Predicate = (), timeout: float | None = None
    ) -> Verdict:
        """PROVED if true for every valid input; REFUTED with a counterexample otherwise.

        An evaluation error counts as "not true"."""
        return self._env._verify(
            "always_true",
            f"always true: {self.source}",
            self,
            None,
            assuming,
            timeout,
            found=Status.REFUTED,
            not_found=Status.PROVED,
        )

    def implies(
        self,
        other: Predicate | str,
        *,
        assuming: Iterable[str | Predicate] | str | Predicate = (),
        timeout: float | None = None,
    ) -> Verdict:
        """PROVED if every input that makes this true also makes `other` true."""
        o = self._env.predicate(other) if isinstance(other, str) else other
        return self._env._verify(
            "implies",
            f"{self.source}  ⟹  {o.source}",
            self,
            o,
            assuming,
            timeout,
            found=Status.REFUTED,
            not_found=Status.PROVED,
        )

    def __and__(self, other: Predicate | str) -> Predicate:
        return self._env.predicate(f"({self.source}) && {_pred_operand(self._env, other)}")

    def __or__(self, other: Predicate | str) -> Predicate:
        return self._env.predicate(f"({self.source}) || {_pred_operand(self._env, other)}")

    def __invert__(self) -> Predicate:
        return self._env.predicate(f"!({self.source})")

    def __bool__(self) -> typing.NoReturn:
        raise TypeError("a Predicate has no truth value; call .evaluate(data) or a verification method")


def _pred_operand(env: Env, other: Predicate | str) -> str:
    if isinstance(other, str):
        return f"({env.predicate(other).source})"
    return _operand(env, other)


def _lookup(w: Mapping[str, Any], path: str) -> tuple[bool, Any]:
    head, *rest = path.split(".")
    if head not in w:
        return False, None
    cur = w[head]
    for part in rest:
        if not isinstance(cur, Mapping) or part not in cur:
            return False, None
        cur = cur[part]
    return True, cur


def _blocking_clause(w: Witness, paths: list[str]) -> str | None:
    # use the most specific paths only (drop prefixes of longer paths)
    leaves = [p for p in paths if not any(q.startswith(p + ".") for q in paths)]
    eqs = []
    for p in leaves:
        ok, val = _lookup(w, p)
        if not ok:
            continue
        try:
            eqs.append(f"{p} == {cel_literal(val)}")
        except TypeError:
            continue
    if not eqs:
        return None
    return "!(" + " && ".join(eqs) + ")"


class Explanation:
    """Per-sub-expression values from one evaluation (see `Expr.explain`)."""

    def __init__(self, source: str, ok: bool, value: Any, nodes: list[tuple[int, int, bool, Any]]):
        self.source = source
        self.ok = ok
        self.value = value
        self.nodes = nodes

    def __iter__(self) -> typing.Iterator[tuple[str, Any]]:
        for a, b, ok, v in self.nodes:
            yield self.source[a:b], (v if ok else f"<error: {v}>")

    def to_json(self) -> list[dict[str, Any]]:
        return [
            {"start": a, "end": b, "text": self.source[a:b], "ok": ok, ("value" if ok else "error"): v}
            for a, b, ok, v in self.nodes
        ]

    def __str__(self) -> str:
        lines = []
        stack: list[int] = []
        seen: set[tuple[int, int]] = set()
        for a, b, ok, v in self.nodes:
            if (a, b) in seen:
                continue
            seen.add((a, b))
            while stack and a >= stack[-1]:
                stack.pop()
            text = self.source[a:b]
            shown = repr(v) if ok else f"error: {v}"
            lines.append(f"{'  ' * len(stack)}{text}  →  {shown}")
            stack.append(b)
        return "\n".join(lines)

    def __repr__(self) -> str:
        return f"Explanation(ok={self.ok}, value={self.value!r})"
