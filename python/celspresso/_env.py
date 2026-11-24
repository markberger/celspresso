from __future__ import annotations

import enum
import fractions
import inspect
import itertools
import math
import typing
from collections.abc import Callable, Iterable, Mapping
from dataclasses import dataclass
from typing import Any, Generic, Literal, TypeVar, overload

from . import _celspresso as _core
from ._errors import CelError, CelEvaluationError, CelSubsetError, CelSyntaxError, CelTypeError, Diagnostic
from ._spec import Spec
from ._types import (
    SchemaBuilder,
    TypeSpec,
    cel_literal,
    contains_fixed,
    from_cel,
    lower,
    type_name,
    witness_to_host,
)
from ._verdict import Bounds, Difference, Extreme, Stats, Status, Verdict, Witness, lookup
from .schema import Struct, TypeRef, _contains_fixed

if typing.TYPE_CHECKING:
    from .adapters import TypeAdapter

__all__ = ["Env", "Explanation", "Expr", "Predicate", "Problem", "RuleCheck", "function"]

T = TypeVar("T")
ErrorMode = Literal["strict", "as_false"]
Assumption = "str | Predicate"


def _option_clash(name: str, value: Any) -> TypeError:
    return TypeError(
        f"{name}={value!r}: '{name}' is an Env option, not a variable. To declare a variable "
        f"named '{name}', pass variables as a mapping: Env({{'{name}': ...}})"
    )


def _check_options(timeout: Any) -> None:
    if timeout is not None and (isinstance(timeout, bool) or not isinstance(timeout, (int, float))):
        raise _option_clash("timeout", timeout)


def _reject_removed_options(more_variables: Mapping[str, Any]) -> None:
    """A removed option passed by keyword would silently declare a variable of that name;
    their old values were bools and ints, never a type, so say what happened instead."""
    for gone in ("schema_constraints", "debug_sample_proofs", "unroll_limit"):
        if isinstance(more_variables.get(gone), (bool, int)):
            raise TypeError(
                f"{gone}={more_variables[gone]!r}: '{gone}' is no longer an Env option. "
                f"To declare a variable named '{gone}', pass variables as a mapping: "
                f"Env({{'{gone}': ...}})"
            )


def _option_list(name: str, value: Any) -> list[Any]:
    """A list-valued option (`structs=`, `adapters=`), which a variable of that name
    would collide with."""
    if isinstance(value, (str, type, Struct, TypeRef)) or not isinstance(value, Iterable):
        raise _option_clash(name, value)
    return list(value)


def _merge_variables(positional: Mapping[str, Any] | None, keywords: dict[str, Any]) -> dict[str, Any]:
    merged = dict(positional or {})
    for n, tp in keywords.items():
        if n in merged:
            raise ValueError(f"variable '{n}' is given both in the mapping and as a keyword")
        merged[n] = tp
    for n in merged:
        if not isinstance(n, str) or not n.isidentifier():
            raise ValueError(f"invalid variable name {n!r}")
    return merged


def _raise_compile(exc: Exception) -> typing.NoReturn:
    kind, items, source = exc.args  # the source that failed (a definition or contract, maybe)
    diags = [Diagnostic(m, a, b, r, kind) for (m, a, b, r) in items]
    cls = {"syntax": CelSyntaxError, "subset": CelSubsetError}.get(kind, CelTypeError)
    raise cls(source, diags) from None


def function(
    fn: Callable[..., Any] | None = None,
    *,
    name: str | None = None,
    ensures: str | None = None,
    total: bool = False,
    tabulate: bool = True,
) -> Any:
    """Mark a Python callable as a CEL function (optionally renaming it).

    Pass the result to `Env.extend(functions=[...])`. Parameter and return types
    come from the type hints. The verifier never calls a function while solving: it
    treats it as opaque, knowing only that it is deterministic, unless you state a
    postcondition. `ensures` is a CEL predicate over the parameters (by name) and
    `result`, e.g. `@function(ensures="result >= 0 && result <= 100")`, trusted at
    every call that does not raise. `total=True` promises the function never raises
    (otherwise a proof must allow for it). Both are trusted, so they must really hold.

    When every parameter has a small finite domain (bool, `Literal`, `Enum`, or an int
    with `ge` and `le`; at most 1024 combinations), the function is called once per
    input when declared and the verifier knows it exactly. Pass `tabulate=False` for a
    function that is slow or has side effects. For logic you want fully verified,
    write it in CEL instead: `env.define(name, body, params={...})`.
    """

    def wrap(f: Callable[..., Any]) -> Callable[..., Any]:
        f.__cel_name__ = name or f.__name__  # type: ignore[attr-defined]
        f.__cel_ensures__ = ensures  # type: ignore[attr-defined]
        f.__cel_total__ = total  # type: ignore[attr-defined]
        f.__cel_tabulate__ = tabulate  # type: ignore[attr-defined]
        return f

    return wrap(fn) if fn is not None else wrap


#: (name, source, parameters or None for a constant definition)
_Def = tuple[str, str, "tuple[tuple[str, TypeSpec], ...] | None"]
#: (arguments, returned normally, result or error message) for one tabulated input
_Row = tuple[list[Any], bool, Any]


@dataclass(frozen=True)
class Limits:
    """Resource caps for evaluating rules you didn't write.

    Exceeding one makes evaluation fail with a `CelEvaluationError`, never hang.
    The defaults suit trusted rules; tighten them for user- or LLM-written ones:
    `Env(..., limits=Limits(max_cost=100_000))`.
    """

    max_cost: int = 10_000_000
    max_iterations: int = 1_000_000
    max_string_len: int = 10_000_000
    max_list_len: int = 1_000_000
    max_regex_size: int = 1 << 20

    def __post_init__(self) -> None:
        for name, v in self.__dict__.items():
            if isinstance(v, bool) or not isinstance(v, int) or v <= 0:
                raise ValueError(f"Limits.{name} must be a positive int, got {v!r}")

    def _spec(self) -> tuple[int, int, int, int, int]:
        return (
            self.max_cost,
            self.max_iterations,
            self.max_string_len,
            self.max_list_len,
            self.max_regex_size,
        )


@dataclass(frozen=True)
class _Fn:
    name: str
    impl: Callable[..., Any]
    params: tuple[TypeSpec, ...]
    result: TypeSpec
    param_names: tuple[str, ...] = ()
    ensures: str | None = None
    total: bool = False
    table: tuple[_Row, ...] | None = None


class Env:
    """An immutable CEL environment: variables, types, functions, definitions.

    >>> env = Env(x=int, name=str)
    >>> env.predicate("x > 3 && name.startsWith('a')").evaluate({"x": 5, "name": "ab"})
    True

    Variables are keyword arguments, or a mapping when a name collides with an option
    (`timeout`, `limits`, `structs`, ...) or is not a Python keyword-safe name:

    >>> Env({"timeout": int}, timeout=2.0).variables
    {'timeout': 'int'}

    Or declare them all as the fields of one model with `Env.from_model(Context)`.

    Expressions are celspresso's subset of CEL: the part the verifier decides exactly and
    quickly (strings, ints, fixed-point numbers, dates, bounded lists and maps, ...).
    Anything else (doubles, bytes, `sort`, time zones, ...) is a compile error that says
    why and what to write instead.
    """

    def __init__(
        self,
        variables: Mapping[str, Any] | None = None,
        /,
        *,
        timeout: float = 5.0,
        limits: Limits | None = None,
        structs: Iterable[Struct | type] = (),
        adapters: Iterable[TypeAdapter] = (),
        **more_variables: Any,
    ) -> None:
        _check_options(timeout)
        _reject_removed_options(more_variables)
        self._sample = 0  # see _debug_options
        if limits is not None and not isinstance(limits, Limits):
            raise _option_clash("limits", limits)
        self._limits = (limits or Limits())._spec()
        variables = _merge_variables(variables, more_variables)
        self._timeout = timeout
        self._schema_constraints = True  # see _debug_options
        self._builder = SchemaBuilder(_option_list("adapters", adapters))
        self._vars: dict[str, tuple[TypeSpec, dict[str, Any] | None]] = {}
        self._fns: dict[str, _Fn] = {}
        self._defs: tuple[_Def, ...] = ()
        self._assumptions: tuple[str, ...] = ()
        self._builder.declare(_option_list("structs", structs))
        for n, tp in variables.items():
            self._vars[n] = self._builder.convert(tp, n)
        self._build()

    @classmethod
    def from_model(
        cls,
        model: type,
        *,
        timeout: float = 5.0,
        limits: Limits | None = None,
        structs: Iterable[Struct | type] = (),
        adapters: Iterable[TypeAdapter] = (),
    ) -> Env:
        """An Env whose variables are the fields of a Pydantic model or dataclass, with
        their types and constraints:

        >>> import dataclasses
        >>> @dataclasses.dataclass
        ... class Context:
        ...     total: int
        ...     tier: str
        >>> Env.from_model(Context).variables
        {'total': 'int', 'tier': 'string'}

        Field names never collide with options, so this suits contexts with many variables.
        Variables are named by field name, not alias: bind data from `model_dump()`, not
        `model_dump(by_alias=True)`."""
        return cls(
            _model_variables(model),
            timeout=timeout,
            limits=limits,
            structs=structs,
            adapters=adapters,
        )

    # -- construction -----------------------------------------------------

    def _clone(self) -> Env:
        e = object.__new__(Env)
        e._timeout = self._timeout
        e._schema_constraints = self._schema_constraints
        e._sample = self._sample
        e._limits = self._limits
        e._builder = self._builder.copy()
        e._vars = dict(self._vars)
        e._fns = dict(self._fns)
        e._defs = self._defs
        e._assumptions = self._assumptions
        return e

    def _build(self) -> None:
        structs = [
            (n, [(f, *lower(s, c)) for f, s, c in fields]) for n, fields in self._builder.structs.items()
        ]
        variables = [(n, *lower(spec, cons)) for n, (spec, cons) in self._vars.items()]
        fns = [
            (
                f.name,
                f"{f.name}_{len(f.params)}",
                False,
                list(f.params),
                f.result,
                (list(f.param_names), f.ensures, f.total, None if f.table is None else list(f.table))
                if f.ensures or f.total or f.table is not None
                else None,
            )
            for f in self._fns.values()
        ]
        try:
            defs = [(n, src, None if ps is None else list(ps)) for n, src, ps in self._defs]
            readers = {n: list(fs) for n, fs in self._builder.readers.items()}
            self._core = _core.Core(structs, variables, fns, defs, readers)
        except _core.CompileError as exc:
            # a definition (or a function's ensures contract) failed to compile
            _raise_compile(exc)
        self._fn_impls = {f.name: f.impl for f in self._fns.values()}
        self._fingerprint = (
            tuple(sorted((n, repr(s)) for n, s in self._vars.items())),
            # struct names alone don't identify a schema: same-named structs may differ
            tuple(sorted((n, repr(fields)) for n, fields in self._builder.structs.items())),
            # ...nor do equal fields: a struct backed by a class decodes witnesses into it
            tuple(
                sorted(
                    (n, repr(k), id(k), type(a).__module__, type(a).__qualname__)
                    for n, (k, a) in self._builder.owners.items()
                )
            ),
            # ...nor does the schema alone: readers change what evaluate sees
            tuple(
                sorted(
                    (n, f, _reader_key(r)) for n, fs in self._builder.readers.items() for f, r in fs.items()
                )
            ),
            tuple(sorted((n, f.ensures or "", f.total, f.table is not None) for n, f in self._fns.items())),
            tuple((n, src, repr(ps)) for n, src, ps in self._defs),
        )

    def extend(
        self,
        variables: Mapping[str, Any] | None = None,
        /,
        *,
        functions: Iterable[Callable[..., Any]] = (),
        timeout: float | None = None,
        structs: Iterable[Struct | type] = (),
        adapters: Iterable[TypeAdapter] = (),
        **more_variables: Any,
    ) -> Env:
        """Return a new Env with more variables, functions, structs or adapters, or new options.

        As with `Env(...)`, pass a mapping for variables whose names clash with options.
        """
        _check_options(timeout)
        _reject_removed_options(more_variables)
        if isinstance(functions, (str, type)) or not isinstance(functions, Iterable):
            raise _option_clash("functions", functions)
        functions = list(functions)
        for f in functions:
            if not callable(f) or isinstance(f, type):
                raise TypeError(f"functions=[...] expects plain callables, got {f!r}")
        if isinstance(more_variables.get("assumptions"), (str, list, tuple, set, frozenset, Predicate)):
            raise TypeError(
                "extend() takes no assumptions (that would declare a variable): use env.assume(...)"
            )
        variables = _merge_variables(variables, more_variables)
        e = self._clone()
        e._builder.add_adapters(_option_list("adapters", adapters))
        e._builder.declare(_option_list("structs", structs))
        for n, tp in variables.items():
            if n in e._vars:
                raise ValueError(f"variable '{n}' is already declared")
            e._vars[n] = e._builder.convert(tp, n)
        for f in functions:
            fn = _function_decl(f, e._builder)
            e._fns[fn.name] = fn
        if timeout is not None:
            e._timeout = timeout
        e._build()
        return e

    def assume(self, *conditions: str | Predicate) -> Env:
        """Return a new Env where every condition is a standing assumption: a fact every
        proof may rely on, which `describe()` tells rule authors about.

        >>> env = Env(x=int).assume("x > 0")
        >>> env.predicate("x != 0").always_true().proved
        True
        """
        for c in conditions:
            if not isinstance(c, (str, Predicate)):
                raise TypeError(f"assume() takes CEL conditions (str or Predicate), got {c!r}")
            if isinstance(c, Predicate) and c.env._fingerprint != self._fingerprint:
                raise ValueError("assume() was given a Predicate from a different Env")
        new = tuple(c if isinstance(c, str) else c.source for c in conditions)
        for c in new:
            self.predicate(c)  # validate now
        e = self._clone()
        e._assumptions = self._assumptions + new
        e._build()
        return e

    def define(self, name: str, source: str, *, params: Mapping[str, Any] | None = None) -> Env:
        """Return a new Env where `name` is a reusable named sub-expression.

        With `params`, the definition is a function written in CEL, called as
        `name(arg, ...)` with arguments in the order given. Unlike a Python `@function`,
        the verifier sees its body, so proofs about it are complete:

        >>> env = Env(score=int).define("clamp", "v < 0 ? 0 : (v > 100 ? 100 : v)", params={"v": int})
        >>> env.predicate("clamp(score) <= 100").always_true().proved
        True
        """
        if not name.isidentifier():
            raise ValueError(f"invalid definition name {name!r}")
        e = self._clone()
        specs: tuple[tuple[str, TypeSpec], ...] | None = None
        if params is None:
            self.compile(source)  # type-check against the current env first
        else:
            for p in params:
                if not p.isidentifier():
                    raise ValueError(f"invalid parameter name {p!r}")
            specs = tuple((p, e._builder.convert(tp, f"{name}({p})")[0]) for p, tp in params.items())
            for p, sp in specs:
                _no_fixed(sp, f"define '{name}' parameter '{p}'", e._builder)
        e._defs = (*self._defs, (name, source, specs))
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
            _raise_compile(exc)
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
        return e if type is None else self._typed(e, type)

    def _typed(self, e: Expr[Any], type: Any) -> Expr[Any]:
        """`e`, checked to give `type` (CelTypeError if not), and carrying it when it says
        more than CEL's type (a fixed-point Decimal is an int in CEL)."""
        want, _ = self._builder.copy().convert(type, "expected type")
        got = e._prog.output_type
        if got != "dyn" and got != lower(want, None)[0]:
            _type_mismatch(e.source, e, type_name(want))
        if want == "bool" and not isinstance(e, Predicate):
            return Predicate(self, e._prog)
        if _contains_fixed(want):
            return Expr(self, e._prog, want)
        return e

    # -- introspection ----------------------------------------------------

    @property
    def variables(self) -> dict[str, str]:
        return {n: type_name(s) for n, (s, _) in self._vars.items()}

    @property
    def assumptions(self) -> tuple[str, ...]:
        return self._assumptions

    def describe(self) -> str:
        """Everything a rule author (person or LLM) needs, as compact text for a prompt.

        Lists the variables, every model's fields with their types and constraints, the
        functions and definitions in scope, the assumed facts, and a short CEL reference.
        """
        out = ["Write one CEL expression (https://cel.dev) over these variables.", "", "Variables:"]
        out += [f"  {n}: {_spec_text(s, c)}" for n, (s, c) in self._vars.items()]
        structs = self._builder.structs
        if structs:
            out += ["", "Types:"]
            for name, fields in structs.items():
                out.append(f"  {name}")
                out += [f"    {f}: {_spec_text(s, c)}" for f, s, c in fields]
        if self._fns:
            out += ["", "Functions:"]
            for f in self._fns.values():
                names = f.param_names or tuple(f"arg{i}" for i in range(len(f.params)))
                ps = ", ".join(f"{n}: {type_name(t)}" for n, t in zip(names, f.params, strict=False))
                line = f"  {f.name}({ps}) -> {type_name(f.result)}"
                out.append(line + (f"  (guarantees: {f.ensures})" if f.ensures else ""))
        if self._defs:
            out += ["", "Definitions (use them by name):"]
            for name, src, params in self._defs:
                body = " ".join(src.split())
                if params is None:
                    out.append(f"  {name} := {body}")
                else:
                    ps = ", ".join(f"{p}: {type_name(t)}" for p, t in params)
                    out.append(f"  {name}({ps}) := {body}")
        if self._assumptions:
            out += ["", "Always true (you may rely on these):"]
            out += [f"  {a}" for a in self._assumptions]
        out += ["", _CEL_REFERENCE]
        specs = [s for s, _ in self._vars.values()] + [s for fs in structs.values() for _, s, _ in fs]
        if any(_contains_fixed(s) for s in specs):
            out.append(
                "  fixed(d, p) is an exact decimal written as an int count of 10^-p units, as are\n"
                "  its bounds above: with fixed(8, 2), 12.34 is 1234 (write price <= 5000, not 50.0)"
            )
        return "\n".join(out)

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
        found: Status = Status.PROVED,
        not_found: Status = Status.REFUTED,
    ) -> Verdict:
        for x in (a, b):
            if x is not None and x._env._fingerprint != self._fingerprint:
                raise ValueError("expressions come from different environments")
        asm_src, asm = self._assumption_progs(assuming, a, b)
        out = _core.verify(
            kind,
            a._prog,
            b._prog if b is not None else None,
            asm,
            int((timeout if timeout is not None else self._timeout) * 1000),
            self._schema_constraints,
            errors,
            self._fn_impls,
            self._sample,
        )
        stats = Stats(out["elapsed_ms"], tuple(out["approximations"]))
        common = {
            "question": question,
            "bounded": out["bounded"],
            "assumptions": tuple(asm_src),
            "stats": stats,
        }
        if out["status"] == "found":
            paths = sorted({p for x in (a, b) if x is not None for p in x.references})
            w = Witness(out["witness"], self._specs(), self._builder, paths)
            try:
                w.to_python()
            except ValueError as exc:  # a validator (or adapter) rejected it: not a real input
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

    def _assumption_progs(
        self, assuming: Iterable[str | Predicate] | str | Predicate, *exprs: Expr[Any] | None
    ) -> tuple[list[str], list[Any]]:
        """This env's assumptions, those of every Env the expressions were compiled in
        (`env.assume(...)` keeps the schema, so they may differ), then `assuming`."""
        if isinstance(assuming, (str, Predicate)):
            assuming = [assuming]
        envs = [self, *(e._env for e in exprs if e is not None)]
        given = [x if isinstance(x, str) else x.source for x in assuming]
        asm_src = list(dict.fromkeys([*(a for env in envs for a in env._assumptions), *given]))
        return asm_src, [self.predicate(s)._prog for s in asm_src]

    def _bounds(
        self, e: Expr[Any], assuming: Iterable[str | Predicate] | str | Predicate, timeout: float | None
    ) -> Bounds:
        if e._env._fingerprint != self._fingerprint:
            raise ValueError("expressions come from different environments")
        asm_src, asm = self._assumption_progs(assuming, e)
        out = _core.bounds(
            e._prog,
            asm,
            int((timeout if timeout is not None else self._timeout) * 1000),
            self._schema_constraints,
            self._fn_impls,
        )
        spec = e._result_spec
        paths = sorted(e.references)

        def end(x: dict[str, Any] | None) -> Extreme | None:
            if x is None:
                return None
            w = Witness(x["witness"], self._specs(), self._builder, paths)
            return Extreme(from_cel(x["value"], spec, self._builder), w, x["attained"], x["sound"])

        return Bounds(
            f"bounds: {e.source}",
            end(out["min"]),
            end(out["max"]),
            out["reason"],
            out["bounded"],
            tuple(asm_src),
            Stats(out["elapsed_ms"], tuple(out["approximations"])),
        )

    def _class_clause(self, w: Witness, exprs: Iterable[Expr[Any]]) -> str | None:
        """A clause excluding every input that sets each atomic condition of `exprs`
        (a boolean sub-expression with no boolean sub-expression inside) the way `w`
        does. Conditions over macro loop variables are skipped; the clause must
        exclude `w` itself, or None is returned."""
        data = w  # raw solver values: replayed without field readers
        values: dict[str, bool | None] = {}
        for e in exprs:
            ex = e.explain(data)
            spans = [(a, b, v) for (a, b, ok, v) in ex.nodes if ok and isinstance(v, bool)]
            usable = [(a, b, v) for (a, b, v) in spans if self._standalone(ex.source[a:b])]
            for a, b, v in usable:
                if any((c, d) != (a, b) and a <= c and d <= b for (c, d, _) in usable):
                    continue  # not atomic
                text = ex.source[a:b].strip()
                values[text] = v if values.get(text, v) == v else None  # conflicting: drop
        atoms = [f"({t}) == {'true' if v else 'false'}" for t, v in sorted(values.items()) if v is not None]
        if not atoms:
            return None
        clause = "!(" + " && ".join(atoms) + ")"
        try:
            excluded = self.predicate(clause).evaluate(data) is False
        except Exception:  # noqa: BLE001 - any failure: use value blocking instead
            return None
        return clause if excluded else None

    def _standalone(self, src: str) -> bool:
        try:
            self.predicate(src)
        except CelError:
            return False
        return True

    def check_rule(
        self,
        rule: str | Expr[Any],
        spec: Spec | Mapping[str, str | Predicate] | Iterable[str | Predicate] = (),
        *,
        timeout: float | None = None,
    ) -> RuleCheck:
        """Vet a rule you didn't write (from a customer, an admin UI or an LLM) before accepting it.

        `spec` is a `Spec`, or just the invariants (a mapping or list of conditions).
        Checks, in order: it compiles (to the spec's `returns` type, if it names one);
        nothing in it is a likely mistake (see `Expr.warnings`); it gives the expected
        result on every example; a true/false rule can fire at all; it can't fail at
        runtime; it implies every invariant (what it must never allow); every `require`
        case implies it (what it must allow); and its result meets every `ensures`
        condition. Invariants and `ensures` keep a rule safe, `require` and `examples`
        keep it useful: without them a rule that allows almost nothing passes. A check
        that comes back UNKNOWN is a problem too, so `.ok` means *proved*.

        A rule may compute any value, not just true or false: an amount, a label, or a
        struct such as `Decision{action: 'refund', amount: ...}` (declare its class with
        `Env(structs=[Decision])`). Invariants and `require` apply only to true/false
        rules; say what any other result must satisfy with `ensures`.
        """
        if not isinstance(spec, Spec):
            spec = Spec(spec)
        # this env's own assumptions apply even to a rule compiled in a sibling Env
        assuming = (*self._assumptions, *spec.assumptions)
        src = rule if isinstance(rule, str) else rule.source
        if isinstance(rule, Expr) and rule._env._fingerprint != self._fingerprint:
            raise ValueError("check_rule was given a rule compiled in a different Env")
        try:
            expr = self.compile(rule) if isinstance(rule, str) else rule
            if spec.returns is not None:
                expr = self._typed(expr, spec.returns)
        except CelError as e:
            return RuleCheck(src, None, (Problem("invalid", str(e)),))
        if not isinstance(expr, Predicate):
            # a rule that computes a value is accepted only by a spec that speaks of values,
            # so a gate written for true/false rules never passes one by accident
            if spec.invariants or spec.require:
                msg = (
                    f"the rule gives {expr.output_type}, not true or false: invariants and require "
                    "apply only to true/false rules (say what its result must satisfy with ensures)"
                )
                return RuleCheck(src, expr, (Problem("invalid", msg),))
            if not spec.ensures and spec.returns is None:
                msg = (
                    f"the rule gives {expr.output_type}, not true or false; to check a rule that "
                    "computes a value, give the spec its type (returns) or conditions on it (ensures)"
                )
                return RuleCheck(src, expr, (Problem("invalid", msg),))
        problems: list[Problem] = [Problem("suspicious", w.rendered) for w in expr.warnings]
        for i, (data, expected) in enumerate(spec.examples):
            try:
                raw = expr._evaluate_raw(data)
            except CelEvaluationError as e:
                why = f"example {i} should give {expected!r}, but evaluation fails: {e}"
                problems.append(Problem("wrong_example", why))
                continue
            try:
                got: Any = expr._to_python(raw)
            except Exception as e:  # noqa: BLE001 - e.g. a value its class's validation rejects
                why = f"example {i} should give {expected!r}, but its result can't be built: {e}"
                problems.append(Problem("wrong_example", why))
                continue
            if not _same_result(got, expected):
                why = f"example {i} should give {expected!r}, but the rule gives {got!r}"
                problems.append(Problem("wrong_example", why))

        def undecided(what: str, v: Verdict, invariant: str | None = None) -> None:
            problems.append(Problem("unverified", f"could not verify {what}: {v.reason}", invariant, v))

        if isinstance(expr, Predicate):
            v = expr.satisfiable(assuming=assuming, timeout=timeout)
            if v.refuted:
                # never true: often because it fails instead (division by zero, overflow, ...)
                err = expr.never_errors(assuming=assuming, timeout=timeout)
                if err.refuted:
                    msg = f"the rule is never true for any valid input: evaluation {_failure(expr, err)}"
                    problems.append(Problem("never_fires", msg, None, err))
                else:
                    problems.append(
                        Problem("never_fires", "the rule can never be true for any valid input", None, v)
                    )
                return RuleCheck(src, expr, tuple(problems))
            if v.unknown:
                undecided("that the rule can fire", v)
        v = expr.never_errors(assuming=assuming, timeout=timeout)
        if v.refuted:
            problems.append(Problem("may_error", f"evaluation {_failure(expr, v)}", None, v))
        elif v.unknown:
            undecided("that the rule never errors", v)
        if isinstance(expr, Predicate):
            for name, inv in spec.invariants.items():
                v = expr.implies(inv, assuming=assuming, timeout=timeout)
                if v.refuted:
                    problems.append(
                        Problem("violates", f"violates '{name}' when {v.counterexample}", name, v)
                    )
                elif v.unknown:
                    undecided(f"'{name}'", v, name)
            for name, req in spec.require.items():
                v = self._as_predicate(req).implies(expr, assuming=assuming, timeout=timeout)
                if v.refuted:
                    msg = f"too narrow: doesn't allow '{name}', e.g. when {v.counterexample}"
                    problems.append(Problem("too_narrow", msg, name, v))
                elif v.unknown:
                    undecided(f"that it allows '{name}'", v, name)
        if spec.ensures:
            problems += self._check_ensures(expr, spec.ensures, assuming, timeout)
        if not isinstance(expr, Predicate):
            problems += self._check_fits(expr, spec, assuming, timeout)
        return RuleCheck(src, expr, tuple(problems))

    def _check_ensures(
        self,
        expr: Expr[Any],
        ensures: Mapping[str, str | Predicate],
        assuming: Iterable[str | Predicate],
        timeout: float | None,
    ) -> list[Problem]:
        """Each `ensures` condition, over the inputs and `result` (the rule's value), holds
        on every valid input on which the rule doesn't fail."""
        problems: list[Problem] = []
        conds = {n: c if isinstance(c, str) else c.source for n, c in ensures.items()}
        for name, v in self._results_meet(expr, conds, assuming, timeout).items():
            if isinstance(v, CelError):
                msg = f"ensures '{name}' doesn't apply to this rule's result ({expr.output_type}): {v}"
                problems.append(Problem("invalid", msg, name))
            elif v.refuted:
                msg = f"violates ensures '{name}' {_when(v)}{_result_note(expr, v)}"
                problems.append(Problem("violates", msg, name, v))
            elif v.unknown:
                problems.append(
                    Problem("unverified", f"could not verify ensures '{name}': {v.reason}", name, v)
                )
        return problems

    def _check_fits(
        self, expr: Expr[Any], spec: Spec, assuming: Iterable[str | Predicate], timeout: float | None
    ) -> list[Problem]:
        """The rule's value meets the constraints of its declared type (and of the structs
        it builds), so it can become a Python value: the verifier assumes them of inputs,
        not of values a rule builds."""
        if spec.returns is not None:
            want, cons = self._builder.copy().convert(spec.returns, "returns")
        else:
            want, cons = expr._result_spec, None
        try:
            fits = _fits("result", "the result", want, cons, self._builder.structs)
        except _Unchecked as e:
            msg = f"could not verify that the result is a valid {type_name(want)}: {e} is recursive"
            return [Problem("unverified", msg)]
        if not fits:
            return []
        conds = dict(fits)
        problems: list[Problem] = []
        for what, v in self._results_meet(expr, conds, assuming, timeout).items():
            if isinstance(v, CelError):
                # e.g. a list field of a struct inside a list the rule built: its size isn't
                # known statically
                why = str(v)
                if "max_length" in why or "can't bound" in why:
                    why = "the verifier can't bound the size of that value where the rule builds it"
                problems.append(Problem("unverified", f"could not verify that {what}: {why}"))
            elif v.refuted:
                msg = f"gives a result that isn't a valid {type_name(want)} {_when(v)}: {what} fails"
                problems.append(Problem("violates", msg, None, v))
            elif v.unknown:
                problems.append(Problem("unverified", f"could not verify that {what}: {v.reason}", None, v))
        return problems

    def _results_meet(
        self,
        expr: Expr[Any],
        conds: Mapping[str, str],
        assuming: Iterable[str | Predicate],
        timeout: float | None,
    ) -> dict[str, Verdict | CelError]:
        """For each named condition over `result` (the rule's value) and the inputs: the
        verdict that it holds wherever the rule has a value, or the condition's compile
        error."""
        if "result" in self._vars or any(n == "result" for n, _, _ in self._defs):
            raise ValueError(
                "ensures refers to the rule's value as 'result', but this Env has a variable "
                "or definition named 'result'"
            )
        # `result`, typed as the rule's value, to compile the conditions with clear errors
        with_result = self._clone()
        with_result._vars["result"] = (expr._result_spec, None)
        with_result._build()

        # the rule's value bound to `result` (cel.bind computes it up front, so with `true`
        # this is false exactly where the rule fails); newlines end any `//` comment
        def bound(cond: str) -> Predicate:
            return self.predicate(f"cel.bind(result, (\n{expr.source}\n), (\n{cond}\n))")

        has_value = bound("true")
        out: dict[str, Verdict | CelError] = {}
        for name, cond in conds.items():
            try:
                holds = bound(cond)
            except CelError as e:
                # report the condition's own error (its spans are in its own text), unless
                # only the bound form fails
                err: CelError = e
                try:
                    with_result.predicate(cond)
                except CelError as own:
                    err = own
                out[name] = err
                continue
            out[name] = has_value.implies(holds, assuming=assuming, timeout=timeout)
        return out

    def _as_predicate(self, p: str | Predicate) -> Predicate:
        return self.predicate(p) if isinstance(p, str) else p


ProblemKind = Literal[
    "invalid",
    "suspicious",
    "wrong_example",
    "never_fires",
    "may_error",
    "violates",
    "too_narrow",
    "unverified",
]


def _reader_key(reader: Callable[[Any], Any]) -> tuple[int, ...]:
    """Identity of what a reader does: a function's code and captured values, so an
    adapter that makes a fresh lambda per build still gives identical Envs."""
    code = getattr(reader, "__code__", None)
    if code is None:
        return (id(reader),)
    cells = getattr(reader, "__closure__", None) or ()
    return (id(code), *(id(c.cell_contents) for c in cells))


def _failure(pred: Expr[Any], v: Verdict) -> str:
    """'fails (division by zero) when x = 0': the witness, and the error it really raises."""
    cause = ""
    if v.witness is not None:
        try:
            pred.evaluate(v.witness)
        except CelEvaluationError as e:
            cause = f" ({e.message})"
        except Exception:  # noqa: BLE001 - the cause is a nicety; the witness is the evidence
            cause = ""
    return f"fails{cause} when {v.witness}"


def _when(v: Verdict) -> str:
    """'when <counterexample>', or 'on every input' for a rule that reads no input."""
    cex = str(v.counterexample or "")
    return f"when {cex}" if cex else "on every input"


def _result_note(expr: Expr[Any], v: Verdict) -> str:
    """': the result is X' for a counterexample, when the rule can be replayed on it."""
    if v.witness is None:
        return ""
    try:
        return f": the result is {expr.evaluate(v.witness)!r}"
    except Exception:  # noqa: BLE001 - the value is a nicety; the witness is the evidence
        return ""


def _same_result(got: Any, expected: Any) -> bool:
    """Whether a rule's value is the expected one, at every level: booleans must match
    exactly (True is not 1), and a struct matches an instance or a mapping of its fields."""
    got, expected = _plain(got), _plain(expected)
    if isinstance(got, (set, frozenset)) or isinstance(expected, (set, frozenset)):
        # a set field matches its items in any order
        if not isinstance(got, (set, frozenset, list, tuple)) or not isinstance(
            expected, (set, frozenset, list, tuple)
        ):
            return False
        rest = list(expected)
        for a in got:
            hit = next((i for i, b in enumerate(rest) if _same_result(a, b)), None)
            if hit is None:
                return False
            rest.pop(hit)
        return not rest
    if isinstance(got, bool) or isinstance(expected, bool):
        return isinstance(got, bool) and isinstance(expected, bool) and got == expected
    if isinstance(got, Mapping) and isinstance(expected, Mapping):
        return got.keys() == expected.keys() and all(_same_result(got[k], expected[k]) for k in got)
    if isinstance(got, (list, tuple)) and isinstance(expected, (list, tuple)):
        return len(got) == len(expected) and all(
            _same_result(a, b) for a, b in zip(got, expected, strict=True)
        )
    return bool(got == expected)


def _plain(value: Any) -> Any:
    """A model or dataclass instance as a dict of its fields, one level down (anything
    else as is): `_same_result` recurses into the fields."""
    import dataclasses

    if isinstance(value, type):
        return value
    if isinstance(value, enum.Enum):
        return value.value
    fields = getattr(type(value), "model_fields", None)
    if isinstance(fields, Mapping):
        return {k: getattr(value, k) for k in fields}
    if dataclasses.is_dataclass(value):
        return {f.name: getattr(value, f.name) for f in dataclasses.fields(value)}
    return value


class _Unchecked(Exception):
    """A result type whose constraints can't all be written as CEL conditions."""


def _fits(
    x: str,
    shown: str,
    spec: TypeSpec,
    cons: Mapping[str, Any] | None,
    structs: Mapping[str, list[tuple[str, TypeSpec, dict[str, Any] | None]]],
    seen: tuple[str, ...] = (),
    depth: int = 0,
) -> list[tuple[str, str]]:
    """(what, CEL condition) for each declared constraint that a value `x` (shown to
    people as `shown`) of `spec` must meet to become a Python value: the field
    constraints of the structs in it, and `cons`. The verifier assumes them of inputs,
    but a value a rule builds must be shown to meet them. Raises _Unchecked for a
    recursive struct, which has no finite set of conditions."""
    spec, low = lower(spec, dict(cons) if cons else None)
    c = dict(low or {})
    out: list[tuple[str, str]] = []

    def sizes() -> None:
        if "min_length" in c:
            out.append((f"{shown} has size >= {c['min_length']}", f"size({x}) >= {c['min_length']}"))
        if "max_length" in c:
            out.append((f"{shown} has size <= {c['max_length']}", f"size({x}) <= {c['max_length']}"))

    if isinstance(spec, str):
        u = "u" if spec == "uint" else ""
        if spec in ("int", "uint"):
            lo, hi = (0, 2**64 - 1) if u else (-(2**63), 2**63 - 1)
            for key in ("ge", "gt", "le", "lt"):
                if key not in c:
                    continue
                # the least (ge, gt) or greatest (le, lt) integer allowed, exactly
                b = c[key] if isinstance(c[key], int) else fractions.Fraction(c[key])
                n = {
                    "ge": math.ceil(b),
                    "gt": math.floor(b) + 1,
                    "le": math.floor(b),
                    "lt": math.ceil(b) - 1,
                }[key]
                op = ">=" if key in ("ge", "gt") else "<="
                if (op == ">=" and n <= lo) or (op == "<=" and n >= hi):
                    continue  # every value of the type meets it
                cond = "false" if not lo <= n <= hi else f"{x} {op} {n}{u}"
                out.append((f"{shown} {op} {n}", cond))
        if "one_of" in c:
            vals = ", ".join(f"{v}{u}" if isinstance(v, int) else cel_literal(v) for v in c["one_of"])
            out.append((f"{shown} is one of {vals}", f"{x} in [{vals}]"))
        sizes()
        if "pattern" in c:
            pat = cel_literal(c["pattern"])
            out.append((f"{shown} matches {pat}", f"{x}.matches({pat})"))
        return out
    kind = spec[0]
    if kind == "nullable":
        inner = _fits(x, shown, spec[1], low, structs, seen, depth)
        return [(w, f"{x} == null || ({cond})") for w, cond in inner]
    if kind in ("list", "map"):
        sizes()
        v = f"_r{depth}"
        if kind == "list":
            item, item_shown, elem = v, f"each item of {shown}", spec[1]
        else:
            item, item_shown, elem = f"{x}[{v}]", f"each value of {shown}", spec[2]
        for w, cond in _fits(item, item_shown, elem, c.get("items"), structs, seen, depth + 1):
            out.append((w, f"{x}.all({v}, {cond})"))
        return out
    if kind == "struct":
        name = spec[1]
        if name in seen:
            raise _Unchecked(name)
        for f, fspec, fcons in structs.get(name, []):
            out += _fits(f"{x}.{f}", f"{shown}.{f}", fspec, fcons, structs, (*seen, name), depth)
    return out


def _joint_env(env: Env, other: Predicate | str) -> Env:
    """`env`, plus the assumptions `other` was compiled under, so `p & q` keeps both."""
    if not isinstance(other, Predicate):
        return env
    extra = [a for a in other._env._assumptions if a not in env._assumptions]
    return env.assume(*extra) if extra else env


def _value_or_error(e: Expr[Any], data: Mapping[str, Any]) -> Any:
    """What `e` gives for `data`: its value, or the CelEvaluationError it raises."""
    try:
        return e.evaluate(data)
    except CelEvaluationError as exc:
        return exc


def _model_variables(model: Any) -> dict[str, Any]:
    """The fields of a Pydantic model or a dataclass, as `Env` variables."""
    import dataclasses

    fields = getattr(model, "model_fields", None)
    if isinstance(model, type) and isinstance(fields, Mapping):  # Pydantic v2
        out: dict[str, Any] = {}
        for name, info in fields.items():
            meta = tuple(getattr(info, "metadata", ()))
            out[name] = typing.Annotated[(info.annotation, *meta)] if meta else info.annotation
        return out
    if isinstance(model, type) and dataclasses.is_dataclass(model):
        try:
            hints = typing.get_type_hints(model, include_extras=True)
        except NameError as exc:
            raise TypeError(f"{model.__name__}: cannot resolve annotation {exc.name!r}") from None
        return {f.name: hints[f.name] for f in dataclasses.fields(model)}
    raise TypeError(f"Env.from_model expects a Pydantic model or dataclass class, got {model!r}")


def _debug_options(
    env: Env, *, sample_proofs: int | None = None, schema_constraints: bool | None = None
) -> Env:
    """Internal: a copy of `env` with testing-only verifier options. `sample_proofs` checks
    each proof against that many random inputs; `schema_constraints=False` stops the prover
    from relying on the schema's constraints (to test that they matter)."""
    e = env._clone()
    if sample_proofs is not None:
        if isinstance(sample_proofs, bool) or not isinstance(sample_proofs, int) or sample_proofs < 0:
            raise TypeError(f"sample_proofs must be a non-negative int, got {sample_proofs!r}")
        e._sample = sample_proofs
    if schema_constraints is not None:
        e._schema_constraints = schema_constraints
    e._build()
    return e


def _spec_text(spec: TypeSpec, cons: Mapping[str, Any] | None) -> str:
    """A type and its constraints, as a rule author needs them."""
    nullable = isinstance(spec, tuple) and spec[0] == "nullable"
    base = spec[1] if nullable else spec
    parts = [type_name(base) + (" or null" if nullable else "")]
    parts += _cons_text(cons)
    return ", ".join(parts)


def _cons_text(cons: Mapping[str, Any] | None) -> list[str]:
    if not cons:
        return []
    out: list[str] = []
    if cons.get("one_of") is not None:
        out.append("one of " + ", ".join(cel_literal(v) for v in cons["one_of"]))
    for key, op in (("ge", ">="), ("gt", ">"), ("le", "<="), ("lt", "<")):
        if cons.get(key) is not None:
            b = cons[key]
            out.append(f"{op} {int(b) if float(b).is_integer() else b}")
    if cons.get("min_length") is not None:
        out.append(f"size >= {cons['min_length']}")
    if cons.get("max_length") is not None:
        out.append(f"size <= {cons['max_length']}")
    if cons.get("pattern") is not None:
        out.append(f"matches {cons['pattern']!r}")
    if cons.get("items"):
        out.append("each item: " + ", ".join(_cons_text(cons["items"])))
    return out


_CEL_REFERENCE = """CEL quick reference:
  logic: a && b, a || b, !a, cond ? x : y        (no 'and', 'or', 'not', 'if')
  compare: == != < <= > >=, x in [1, 2], k in map  (no '=' or '===')
  literals: true, false, null, 42, 'text', [1, 2], {'k': 1}    (no doubles like 4.2)
  strings: size(s), s.contains(t), s.startsWith(t), s.endsWith(t), s.matches(regex), s.lowerAscii()
  lists: size(l), l.all(x, p), l.exists(x, p), l.exists_one(x, p), l.filter(x, p), l.map(x, f)
  fields: m.f; has(m.f) tests presence; ints are 64-bit and overflow is an error"""


@dataclass(frozen=True)
class Problem:
    """One reason a rule was not accepted. `verdict` holds the evidence, when there is one."""

    kind: ProblemKind
    message: str
    invariant: str | None = None
    verdict: Verdict | None = None


@dataclass(frozen=True)
class RuleCheck:
    """The result of `Env.check_rule`. `str()` is a report fit for a person or an LLM."""

    source: str
    rule: Expr[Any] | None
    problems: tuple[Problem, ...]

    @property
    def ok(self) -> bool:
        """True only if every check was *proved*: an UNKNOWN counts as a problem."""
        return not self.problems

    def __bool__(self) -> typing.NoReturn:
        raise TypeError("use RuleCheck.ok (a RuleCheck has no truth value, like a Verdict)")

    def __str__(self) -> str:
        if self.ok:
            return "accepted: every check passed"
        return "rejected:\n" + "\n".join("- " + p.message.replace("\n", "\n  ") for p in self.problems)


def _type_mismatch(source: str, e: Expr[Any], want: str) -> typing.NoReturn:
    msg = f"expression has type {e.output_type}, expected {want}"
    raise CelTypeError(source, [Diagnostic(msg, 0, len(source), f"{msg}\n  | {source}", "type")])


#: Most inputs a host function is called on to tabulate it.
TABULATE_LIMIT = 1024


def _domain(spec: TypeSpec, cons: Mapping[str, Any] | None) -> list[Any] | None:
    """Every value a parameter can take, if that is a short finite list."""
    if spec == "bool":
        return [False, True]
    if cons and cons.get("one_of") is not None:
        return list(cons["one_of"])
    if spec in ("int", "uint") and cons:
        lo = math.ceil(cons["ge"]) if cons.get("ge") is not None else None
        if cons.get("gt") is not None:
            lo = math.floor(cons["gt"]) + 1
        hi = math.floor(cons["le"]) if cons.get("le") is not None else None
        if cons.get("lt") is not None:
            hi = math.ceil(cons["lt"]) - 1
        if spec == "uint":
            lo = max(lo or 0, 0)
        if lo is not None and hi is not None and hi - lo < TABULATE_LIMIT:
            return list(range(lo, hi + 1))
    return None


def _call_row(name: str, f: Callable[..., Any], args: tuple[Any, ...]) -> _Row:
    try:
        return (list(args), True, f(*args))
    except Exception as exc:  # noqa: BLE001 - mirrors a runtime call that raises
        return (list(args), False, f"function '{name}' raised {type(exc).__name__}")


def _tabulate(name: str, f: Callable[..., Any], domains: list[list[Any] | None]) -> tuple[_Row, ...] | None:
    """Call `f` on every input, if the inputs are few. A raising input is an erroring call."""
    finite = [d for d in domains if d is not None]
    if len(finite) != len(domains) or math.prod(len(d) for d in finite) > TABULATE_LIMIT:
        return None
    return tuple(_call_row(name, f, args) for args in itertools.product(*finite))


def _no_fixed(spec: TypeSpec, where: str, builder: SchemaBuilder) -> None:
    if contains_fixed(spec, builder):
        raise TypeError(
            f"{where}: fixed-point (Decimal) values can't cross a function boundary yet; pass cents as int"
        )


def _function_decl(f: Callable[..., Any], builder: SchemaBuilder) -> _Fn:
    name = getattr(f, "__cel_name__", None) or f.__name__
    hints = typing.get_type_hints(f, include_extras=True)
    sig = inspect.signature(f)
    params: list[TypeSpec] = []
    domains: list[list[Any] | None] = []
    for p in sig.parameters.values():
        if p.name not in hints:
            raise TypeError(f"function '{name}': parameter '{p.name}' needs a type hint")
        spec, cons = builder.convert(hints[p.name], f"{name}({p.name})")
        _no_fixed(spec, f"function '{name}' parameter '{p.name}'", builder)
        params.append(spec)
        domains.append(_domain(spec, cons))
    if "return" not in hints:
        raise TypeError(f"function '{name}' needs a return type hint")
    result = builder.convert(hints["return"], f"{name} result")[0]
    _no_fixed(result, f"function '{name}' result", builder)
    names = tuple(sig.parameters)
    ensures = getattr(f, "__cel_ensures__", None)
    if ensures is not None and "result" in names:
        raise TypeError(f"function '{name}': a parameter named 'result' clashes with ensures")
    table = _tabulate(name, f, domains) if getattr(f, "__cel_tabulate__", True) else None
    total = bool(getattr(f, "__cel_total__", False))
    return _Fn(name, f, tuple(params), result, names, ensures, total, table)


def _operand(env: Env, x: Any) -> str:
    if isinstance(x, Expr):
        if x._env._fingerprint != env._fingerprint:
            raise ValueError("expressions come from different environments")
        return f"({x.source})"
    return cel_literal(x)


class Expr(Generic[T]):
    """A compiled, type-checked CEL expression producing a `T`."""

    __slots__ = ("_env", "_prog", "_spec")

    def __init__(self, env: Env, prog: Any, spec: TypeSpec | None = None) -> None:
        self._env = env
        self._prog = prog
        # the result type asked for in env.expr, when it says more than the core's
        # (a fixed-point Decimal is an int in CEL)
        self._spec = spec

    @property
    def _result_spec(self) -> TypeSpec:
        return self._spec if self._spec is not None else self._prog.output_type

    # -- metadata ---------------------------------------------------------

    @property
    def source(self) -> str:
        return self._prog.source

    @property
    def canonical(self) -> str:
        """Normalized text of the expression, with definitions expanded, for display and
        comparison. It is not guaranteed to parse as CEL: expanded definitions appear as
        internal bindings (`cel.bind(@arg:...)`)."""
        return self._prog.canonical

    @property
    def output_type(self) -> str:
        return type_name(self._spec) if self._spec is not None else self._prog.output_type_name

    @property
    def references(self) -> list[str]:
        """Variables and field paths this expression reads, e.g. ['user.age']."""
        return self._prog.references

    @property
    def warnings(self) -> list[Diagnostic]:
        """Code that type-checks but is almost certainly a mistake.

        For example `order.tier == 'Gold'` when the schema says the tier is 'standard'
        or 'gold': the comparison can never be true.
        """
        return [Diagnostic(m, a, b, r, "lint") for (m, a, b, r) in self._prog.lint()]

    @property
    def env(self) -> Env:
        return self._env

    def __repr__(self) -> str:
        return f"{type(self).__name__}({self.source!r}, type={self.output_type})"

    def __hash__(self) -> int:
        return hash((self._env._fingerprint, self.canonical, repr(self._spec)))

    def __eq__(self, other: object) -> bool:
        """Syntactic identity: same environment and same canonical text.

        This is *not* semantic equality (`x > 1` and `1 < x` are different
        objects that mean the same thing); use `.equivalent()` for that, and
        `.eq()` to build the CEL comparison `a == b`.
        """
        if not isinstance(other, Expr):
            return NotImplemented
        return self.same_as(other)

    def same_as(self, other: Expr[Any]) -> bool:
        """Syntactic identity (same env, same canonical text); the same as `==`."""
        return (
            self._env._fingerprint == other._env._fingerprint
            and self.canonical == other.canonical
            and self._spec == other._spec
        )

    # -- evaluation -------------------------------------------------------

    def evaluate(self, data: Mapping[str, Any] | None = None) -> T:
        """Evaluate against a mapping of variable values (models, dicts, scalars).

        A `Witness` from a verdict can be passed as is: its values are the solver's raw
        data, so fields are read by name, not by their custom readers (`schema.Field`).
        Pass the Witness itself: `dict(w)` or `w.to_python()` is treated as host data,
        and readers run on it."""
        return self._to_python(self._evaluate_raw(data))

    def _evaluate_raw(self, data: Mapping[str, Any] | None) -> Any:
        """The CEL value `e` gives for `data`, before conversion to the result type."""
        try:
            return self._prog.evaluate(
                self._host(data), self._env._fn_impls, self._env._limits, self._readers(data)
            )
        except _core.EvalError as exc:
            msg, eid, a, b, rendered = exc.args
            raise CelEvaluationError(msg, eid, (a, b), rendered) from None

    def _to_python(self, raw: Any) -> T:
        return from_cel(raw, self._result_spec, self._env._builder)

    def explain(self, data: Mapping[str, Any] | None = None) -> Explanation:
        """Evaluate and record the value of every sub-expression."""
        ok, value, nodes = self._prog.explain(
            self._host(data), self._env._fn_impls, self._env._limits, self._readers(data)
        )
        return Explanation(self.source, ok, value, [(a, b, k, v) for (a, b, k, v) in nodes])

    def _host(self, data: Mapping[str, Any] | None) -> dict[str, Any]:
        if not isinstance(data, Witness):
            return dict(data or {})
        # a witness holds raw CEL values: give fixed-point units back as Decimals
        specs = self._env._specs()
        return {
            k: witness_to_host(v, specs[k], self._env._builder) if k in specs else v for k, v in data.items()
        }

    def _readers(self, data: Mapping[str, Any] | None) -> dict[str, dict[str, Any]] | None:
        if isinstance(data, Witness) or not self._env._builder.readers:
            return None
        return self._env._builder.readers

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

    def never_errors(
        self, *, assuming: Iterable[str | Predicate] | str | Predicate = (), timeout: float | None = None
    ) -> Verdict:
        """PROVED if evaluation can't fail (division by zero, overflow, a missing key, ...)
        on any valid input; REFUTED with an input that makes it fail otherwise."""
        return self._env._verify(
            "can_error",
            f"never errors: {self.source}",
            self,
            None,
            assuming,
            timeout,
            found=Status.REFUTED,
            not_found=Status.PROVED,
        )

    def can_equal(
        self,
        value: Any,
        *,
        assuming: Iterable[str | Predicate] | str | Predicate = (),
        timeout: float | None = None,
    ) -> Verdict:
        """PROVED, with an example, if some valid input makes the expression equal `value`."""
        return self.eq(value).satisfiable(assuming=assuming, timeout=timeout)

    def bounds(
        self, *, assuming: Iterable[str | Predicate] | str | Predicate = (), timeout: float | None = None
    ) -> Bounds:
        """The smallest and largest values over every valid input on which the expression
        does not error: `limit.bounds().expect() == (10, 1000)`. Integer, uint, date,
        timestamp and duration expressions only (found with Z3 Optimize, then proved)."""
        return self._env._bounds(self, assuming, timeout)

    def diff(
        self,
        other: Expr[Any],
        *,
        limit: int = 5,
        assuming: Iterable[str | Predicate] | str | Predicate = (),
        timeout: float | None = None,
    ) -> list[Difference]:
        """Up to `limit` inputs on which the two expressions disagree (and that satisfy
        every assumption), each with what both give for it. Each shows a different
        reason: no two set every condition in the expressions the same way."""
        if isinstance(assuming, (str, Predicate)):
            assuming = [assuming]
        base: list[str | Predicate] = list(assuming)
        found: list[Difference] = []
        blockers: list[str] = []
        paths = sorted(set(self.references) | set(other.references))
        while len(found) < limit:
            v = self.equivalent(other, assuming=[*base, *blockers], timeout=timeout)
            if not v.refuted or v.witness is None:
                break
            found.append(
                Difference(v.witness, _value_or_error(self, v.witness), _value_or_error(other, v.witness))
            )
            # block the witness's whole behaviour class (same truth value for every
            # condition), so each result shows a different reason; fall back to its values
            clause = self._env._class_clause(v.witness, (self, other)) or _blocking_clause(v.witness, paths)
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
        """PROVED, with an example, if some valid input makes this true; REFUTED if none can."""
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
        """PROVED if every input that makes this true also makes `other` true; REFUTED
        with a counterexample otherwise."""
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
        operand = _pred_operand(self._env, other)
        return _joint_env(self._env, other).predicate(f"({self.source}) && {operand}")

    def __or__(self, other: Predicate | str) -> Predicate:
        operand = _pred_operand(self._env, other)
        return _joint_env(self._env, other).predicate(f"({self.source}) || {operand}")

    def __invert__(self) -> Predicate:
        return self._env.predicate(f"!({self.source})")

    def __bool__(self) -> typing.NoReturn:
        raise TypeError("a Predicate has no truth value; call .evaluate(data) or a verification method")


def _pred_operand(env: Env, other: Predicate | str) -> str:
    if isinstance(other, str):
        return f"({env.predicate(other).source})"
    return _operand(env, other)


_lookup = lookup


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
