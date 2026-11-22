# Tech debt

Known issues we've chosen to fix later. Each entry says how to reproduce it, why it was
deferred, and what a fix looks like. Remove an entry in the commit that fixes it.

## Schema and types

### Numeric bounds are doubles, so large int bounds are rejected rather than exact
`Constraints(ge=2**63 - 1)` raises "not exactly representable as a double". The core's
`Constraints` (`crates/celspresso-check/src/decls.rs`) stores `ge/gt/le/lt` as `f64`, and
the validator and the Z3 encoding read them as such. The Pydantic path converts with
`float()` the same way, but there it rounds silently instead of raising.
- *Deferred because* bounds above 2**53 are rare, and an exact fix touches all the crates.
- *Fix:* store bounds as an enum `Int(i128) | Double(f64)` in the core, and pass Python
  ints through unconverted.
- *Found:* review of `celspresso.schema` (M1).

### Pydantic bounds on date, datetime and timedelta fields crash
`Annotated[date, Field(ge=date(2020, 1, 1))]` raises `TypeError: float() argument must
be ... not 'datetime.date'` while the Env is built. `_metadata_constraints` calls
`float()` on every bound.
- *Fix:* map temporal bounds to day numbers or epoch times in the encoding, or else reject
  them with a clear message naming the field.

### Constraints on top-level variables aren't checked against their type
`Env(x=Annotated[str, annotated_types.Ge(3)])` is accepted. The bound is silently ignored
by the prover. Struct fields (declared, or from an adapter) are checked by
`_check_constraints`, but variables never go through it.
- *Fix:* run `_check_constraints` on the result of `SchemaBuilder.convert` for variables,
  `define` params and function signatures.

### Witnesses for Pydantic models with field aliases fail to decode
`full_name: str = Field(alias="fullName")` gives UNKNOWN with "witness fails model
validation", because `PydanticAdapter.decode` passes `model_validate` the field names.
- *Fix:* call `model_validate(data, by_name=True)` (Pydantic ≥ 2.11), or else map names to
  aliases from `model_fields`.

### A Pydantic model can't contain a type from a custom adapter
Pydantic refuses to build a model whose field is a foreign type unless
`arbitrary_types_allowed` is set. Even then, `model_validate` would reject the value the
adapter decoded. Composition works in one direction only: adapter structs and
dataclasses can contain Pydantic models, but not the other way round.
- *Fix:* likely documentation only. Optionally, offer a `decode` hook that builds models
  with `model_construct`.

### String annotations on local classes can only name classes already registered
A dataclass defined inside a function, with `from __future__ import annotations`, that
names another local class fails ("cannot resolve annotation 'X'") unless X is already
registered in the Env. The error says what to do.
- *Fix:* resolve annotations lazily, after every variable's class has been registered.

### Adapters can decode structs only
`TypeAdapter.decode` is called only for structs. A type-level mapping such as
`Cents → T.int` can't turn witness values back into its own type. M4 (`T.fixed` with a
`Decimal` codec) needs this.
- *Fix:* record which adapter owns each converted position, and call a `decode_value`
  hook there.

### Field readers run eagerly, for every reachable field
Each evaluation converts every object reachable from the variables, so every field's
`reader` runs even when the expression never reads that field. With Django, that means
one query per reverse relation per object (N+1 across lists) unless the caller
prefetches. This is documented on `schema.Field` as the contract.
- *Fix:* convert only the field paths the program references (`Program.references`),
  or convert struct fields lazily on first access. Either changes when, and how often,
  readers run, so do it before cortado depends on the current behaviour.
- *Found:* M3 review.

### Host function results ignore the declared result type
A function annotated `-> Order` has its result converted by `infer_value`, so the
`Order` struct's readers (and its field types) are not used, and a non-dict object
fails with "returned an unsupported value".
- *Fix:* convert results with `value_from_py` against the declared result type and the
  readers, or reject struct result types.
- *Found:* M3 review (predates M3).

## Verifier

### Comprehensions over a nullable list are not modeled
`s.c == null || s.c.all(x, x.startsWith('x'))` with `c: list(string)?` returns UNKNOWN,
with "comprehension over this range is not yet modeled". The same comprehension over a
non-nullable list works.
- *Fix:* in the encoder, unwrap a nullable range under the guard that it isn't null.

### Common string functions are not modeled, so form-filling proofs come back UNKNOWN
In the claim-form walkthrough, `upperAscii`, `string(int)` and `split` all made proofs
come back UNKNOWN ("depends on 'upperAscii', which the verifier doesn't model yet").
This includes `can_error()` over the whole fill spec. These functions are everywhere in
form filling (names in caps, money formatting).
- *Fix:* add encodings. `size(upperAscii(s)) == size(s)`, together with per-character
  mapping axioms, covers lengths. `string(int)` can be encoded with Z3's `int.to.str`,
  plus a sign case. `split` is harder: a bounded unrolling, or an uninterpreted function
  with length axioms.
- *Found:* claim-form walkthrough, while writing a usage example.

## Language

### `date` has no month or day accessors
`date` supports only `year()`, `ageOn()` and `daysUntil()`. So a date of birth can't be
formatted into the `MM DD YY` boxes that forms use. The timestamp accessors
(`getMonth`, `getDayOfMonth`) aren't declared for `date`.
- *Fix:* declare `getMonth`/`getDayOfMonth`/`getDayOfWeek` (and maybe `format`) for
  `date`, with day-number encodings in the verifier.
- *Found:* claim-form walkthrough.

## API surface

### `Env` and `Expr` aren't picklable
The design says they pickle as (schema references, source), so `ProcessPoolExecutor`
works. Neither defines `__reduce__`, and the Rust `Core` and `Program` can't be pickled.
- *Fix:* `Env.__reduce__` should rebuild from its constructor inputs (classes pickled by
  reference, plus `structs`, `adapters`, definitions and options). `Expr.__reduce__`
  should be `(env, source, kind, type)`.

### The CLI's `vars = {...}` can't declare structs
Rule files with inline `vars` accept only type names, so declared structs and adapters
need `env = "module:attr"`. This is acceptable for now.
