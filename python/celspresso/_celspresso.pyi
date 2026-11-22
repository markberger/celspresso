"""Native core (Rust). Private: use the `celspresso` package API instead."""

from typing import Any, TypeAlias

TypeSpec: TypeAlias = Any
Constraints: TypeAlias = dict[str, Any] | None

class CompileError(Exception): ...
class EvalError(Exception): ...

class Program:
    @property
    def source(self) -> str: ...
    @property
    def canonical(self) -> str: ...
    @property
    def output_type(self) -> TypeSpec: ...
    @property
    def output_type_name(self) -> str: ...
    @property
    def references(self) -> list[str]: ...
    def evaluate(
        self,
        vars: dict[str, Any],
        functions: dict[str, Any] | None = None,
        limits: tuple[int, int, int, int, int] | None = None,
    ) -> Any: ...
    def explain(
        self,
        vars: dict[str, Any],
        functions: dict[str, Any] | None = None,
        limits: tuple[int, int, int, int, int] | None = None,
    ) -> tuple[bool, Any, list[tuple[int, int, bool, Any]]]: ...

#: (parameter names, ensures source, total, table rows of (args, ok, result or error))
_ContractSpec = tuple[list[str], str | None, bool, list[tuple[list[Any], bool, Any]] | None]

class Core:
    def __init__(
        self,
        structs: list[tuple[str, list[tuple[str, TypeSpec, Constraints]]]],
        vars: list[tuple[str, TypeSpec, Constraints]],
        functions: list[tuple[str, str, bool, list[TypeSpec], TypeSpec, _ContractSpec | None]],
        defs: list[tuple[str, str, list[tuple[str, TypeSpec]] | None]],
    ) -> None: ...
    def compile(self, source: str) -> Program: ...
    def definition_names(self) -> list[str]: ...

def bounds(
    a: Program,
    assumptions: list[Program],
    timeout_ms: int,
    unroll_limit: int,
    schema_constraints: bool,
    functions: dict[str, Any] | None = None,
) -> dict[str, Any]: ...
def verify(
    kind: str,
    a: Program,
    b: Program | None,
    assumptions: list[Program],
    timeout_ms: int,
    unroll_limit: int,
    schema_constraints: bool,
    errors: str,
    functions: dict[str, Any] | None = None,
    sample_proofs: int = 0,
) -> dict[str, Any]: ...
