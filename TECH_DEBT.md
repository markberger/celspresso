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
`Cents → T.int` can't turn witness values back into its own type. (`T.fixed` doesn't need
this: the builder itself decodes it.)
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

### Fixed-point results without an expected type come back in units
`env.compile("order.total").evaluate(...)` returns `1234`, not `Decimal("12.34")`: CEL's
type for a fixed-point field is `int`, and only `env.expr(src, T.fixed(...))` says
otherwise. CEL also lets a rule add a `fixed(8, 2)` to a `fixed(8, 3)` or to a count.
- *Fix:* track the scale through the checker (a `fixed` type that unifies only with
  itself and int literals), so results and mistakes are found without a hint.
- *Found:* M4.

### `T.fixed` allows at most 15 digits
`NUMERIC(18, 2)` and `NUMERIC(19, 4)`, common money columns, are rejected. The digit
bound ±(10**digits − 1) becomes a constraint, and constraints are doubles (see the
first entry), which are exact only up to 2**53.
- *Fix:* the exact-bounds fix above; then allow up to 18 digits (int64 units).
- *Found:* M4 review.

### Fixed-point values have rough edges outside the main path
- `adapters.constraints_from` turns a Decimal bound into an unscaled float and drops
  `max_digits`/`decimal_places`; a third-party adapter should pass the annotation
  (`Annotated[Decimal, ...]`) to `ctx.field` instead, as the Pydantic adapter does.
- `Annotated[T.fixed(8, 2), Field(ge=Decimal("1.00"))]` reads the Decimal bound as units.
- Witnesses and messages print raw units (`order.total = 35538376`, "must be <=
  99999999"), not decimals.
- `env.expr("x", T.fixed(8, 4))` on a `fixed(8, 2)` variable rescales silently (a
  case of the scale mixing above).
- A host function with an untyped parameter (`v: object`) receives raw units.
- `T.fixed(5, 5)` accepts 0, which Pydantic's `max_digits=5, decimal_places=5` rejects,
  so a witness of 0 can't go through `to_python`.
- *Fix:* scale or reject Decimal bounds on `T.fixed`; render fixed witness values with
  their decimal form.
- *Found:* M4 review.

## Verifier

### Comprehensions over a nullable list are not modeled
`s.c == null || s.c.all(x, x.startsWith('x'))` with `c: list(string)?` returns UNKNOWN,
with "comprehension over this range is not yet modeled". The same comprehension over a
non-nullable list works.
- *Fix:* in the encoder, unwrap a nullable range under the guard that it isn't null.

### The subset leaves out some useful formatting builtins
Every `Env` accepts only celspresso's CEL subset (`crates/celspresso-verify/src/subset.rs`): builtins are
allowed by overload id after probing, and everything else is a compile error. Left out
for now but worth adding once modeled and measured: `trim`, `replace` and `format` with
literal arguments, `string()` of dates, timestamps and durations, and `split` with a
limit. Also:
- Errors in a definition, `ensures` contract or assumption say "1 error in CEL
  expression" without naming which definition or contract it was.
- Host functions returning bytes are accepted; their verdicts are UNKNOWN (opaque).
- Fixed-offset time zones (`at.getHours('+01:00')`) are modeled exactly but rejected
  with every `*_with_tz` overload; a literal fixed offset could be allowed.
- `matches('^foo$|^bar$')` (anchors inside a top-level alternation) is rejected by both
  the profile and the translator; translating branch by branch would accept it.
- Doubles are rejected everywhere (use fixed-point). The evaluator and verifier still
  implement them for the conformance suite; that code is now unreachable from Python.
- Integer multiplication of two variables stays in (Z3 Int, range-checked). Measured in
  `benchmarks/bench_mul.py`: 40/42 decided, worst ~400 ms; a 64-bit bit-vector encoding
  decided 30/42. Only factoring-style questions (`a * b == 1000003` with wide bounds)
  time out. A static "one side constant" rule would reject 13 of the 14 shapes.
- `ageOn` is allowed although satisfiability can take seconds; `string(int)` relating two
  differently computed numbers can reach the timeout (see the cents benchmark case).
- Values of type `dyn` (`Any` fields, host functions returning `Any`, `dyn(x)`,
  heterogeneous literals like `[1, 'a']`) are rejected where they originate.
  `dict[str, Any]` can still be tested with `in`/`size`, but its values can't be used.
- `Env(d=float)` is accepted though every use of `d` is an error; it could fail at
  construction. `describe()` still lists such variables without saying so.
- `o.?r` on an optional double field is rejected even when only `.hasValue()` is used.
- `[n, null]` and `n > 0 ? 1 : null` type as dyn and are rejected, while `[p.nick, null]`
  (a nullable field) is accepted; the checker could join int and null into `int?`.
- The verifier answers UNSAT for `[1, 'a'][0] == 1` (heterogeneous list, true at
  runtime). The subset rejects it now, but the encoder bug remains for the Rust
  conformance path; fix it before allowing any dyn back in.
- `matches` patterns are limited to 16 ranges per character class, so Unicode `\d`, `\w`
  and `\p{..}` are rejected (`^\d{5}$` took 4.5 s to come back UNKNOWN; `\p{L}+` ran far
  past the 5 s timeout, so the solver timeout isn't always honored either).
- *Fix:* model the builtins above, measure with `benchmarks/bench_strings.py`, add their
  ids to `ALLOWED` or `LITERAL_ARG`.

### Simple in-profile string questions still time out
The profile promises fast, exact answers, but these come back UNKNOWN at the 5 s timeout
(second subset review):
- Fixed-count regex repetition with a literal `contains`/`indexOf`/`split`:
  `s.matches('^[a-z]{12}$') && !s.contains('q')`. The same fact as `!s.matches('q')`
  takes 0.1 s, so the encoding of `contains` with a literal needle is at fault.
- Concatenated `string(int)`s: `string(n) + '-' + string(k) == '12-3'` with n, k in
  [0, 99]; date formatting from accessors; `xs.map(x, x.upperAscii()).join(',')`.
- `s.upperAscii() == 'ABCDEFGH'` (case mapping is exact for 4 characters only).
- *Fix:* encode literal-needle `contains`/`startsWith`/`endsWith` as regex membership;
  digit-count lemmas or explicit digits for bounded ints; exact bounded case mapping
  (or allow case mapping only within `max_length` ≤ 4). Track with the rewrite corpus.

### The contract fuzzer's known UNKNOWNs
`benchmarks/fuzz_contract.py --gate` (full `check.sh`) lists the in-subset questions that are
still UNKNOWN in `benchmarks/contract_known.txt`; each is a contract bug. Current causes:
- split + join of a string longer than ~4 characters: even `s.split(' ').join('')`
  equivalent to itself times out (max_length 6: >10 s at any slot count; 4: 1.9 s at 5
  slots, 8.4 s at 8). Each side gets its own split encoding.
- case mapping beyond 4 characters (above), and `lowerAscii`/`upperAscii` under
  `contains`/`endsWith`/`matches`, which also make up most of the fuzzer's slow verdicts.
- *Fix:* encode structurally identical subexpressions once (hash-cons by canonical AST
  under the same bindings), so `a <=> a` and shared subterms are free; a cheaper split
  encoding for a literal one-character separator; the case-mapping fix above.
- *Found:* contract fuzzer (fuzzer milestone). The fuzzer also found that split used
  `unroll_limit` slots on bounded strings (now grown up to 32 slots until no overflow is
  possible) and that overflowing split models gave witnesses that never replayed (now
  excluded from the solve).
- `bounds()` has neither the split retry nor the no-overflow assertion, so bounds of a
  split are never marked sound: `s.split(',').size()` with max_length 8 gives an unproven
  `[1, 5]` where the true max is 9 (review of the fuzzer milestone).

### `\d`, `\w`, `\s` and `\b` are Unicode-aware, unlike RE2
CEL regexes are RE2, where the Perl classes are ASCII-only. The evaluator (`regex` crate)
and the verifier (`regex-syntax`) both use Unicode classes, so they agree with each other
but not with cel-go on non-ASCII input (`'٣'.matches('\\d')` is true here, false in cel-go).
Fixing it would also make `\d` fast to verify (one range).
- *Fix:* rewrite Perl classes to their ASCII forms in the regex AST before both the
  evaluator and the verifier see them; add conformance-style tests.

### Some string functions are still not modeled
`trim`, `replace`, `format`, `substring`-free `charAt` loops, `split` with a limit or an
empty or non-constant separator, `reverse` and `quote` return UNKNOWN ("depends on
'trim', which the verifier doesn't model yet"). `lowerAscii`/`upperAscii`, `string()` of
ints, uints and bools, `int()`/`uint()` of strings, `join` and `split(sep)` are modeled.
Remaining limits of those:
- `lowerAscii`/`upperAscii` pin only the first 4 characters of a non-literal string
  (each extra character costs solver time). Facts about longer strings that depend on
  later characters may be UNKNOWN; counterexamples are always replayed, so never wrong.
- `split` uses `unroll_limit` slots. If the assumptions allow more pieces (an unbounded
  string, or `max_length` above the limit), a proof is UNKNOWN even when it holds for
  any number of pieces (`size(t.split(',')) >= 1`).
- `split` always uses `unroll_limit` slots, even when `max_length` bounds the string;
  sizing the slots from the bound (as list inputs do) would avoid raising the limit by hand.
- Overflow conditions are not guarded by whether a split is reached (an inactive
  comprehension step, a filtered-out piece), and assumptions that read a split are left
  out of the overflow check. Both only turn provable results into UNKNOWN.
- Proofs and UNSATs about `int(t)` on an unbounded `t` often run to the timeout (Z3's
  `str.to_int` is weak); asserting `t ∈ [0-9]+` on success may help, unmeasured.
- A review fuzz run saw one nested-split query run far past its timeout; not reproduced.
- *Fix:* `trim` via a regex over the whitespace class; `format` for constant format
  strings; lazy refinement of case-mapping axioms when a witness doesn't replay.
- *Found:* claim-form walkthrough; partly fixed in the string-functions milestone.

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
