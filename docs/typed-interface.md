# Typed interface (M14)

LeanDB programs as values: a read has a pure meaning over `DbState`, and
execution is one deferred snapshot. Writes and transaction programs have
the same shape: a failure type derived from the schema, a pure meaning,
and `run` that equals that meaning on well-formed states.

## Part A

**Schema symbols**, declared next to the entity:

- `unique% T.name := field` or `unique% T.name := (f1, f2, …)` — generates
  `Unique α` (one constructor per index), `Unique.Key`, the SQLite unique
  index, and `HasUnique`. A table with no unique indexes keeps
  `Unique α := Empty`, so `IsEmpty` is found.
- `schema% S := T1, T2, …` — marker type `S` with `IsSchema S`, plus
  `ForeignKey α` from `Ref` fields, `ListField α` from child lists, and
  `ReferencedBy S α` for inbound keys. `typed% T` generates the same
  symbols for one entity without a schema marker.
- `cascade% T.field` — that `Ref` is `ON DELETE CASCADE` (default is
  RESTRICT). Must precede `deriving LeanDb.Entity`, so DDL, meaning, and
  `DeleteError` share the same fact.
- `Checked α := { v : α // Invariant α v }`, built by `Entity.check` /
  `Checked.check` at runtime or `Checked.of` from a proof.

Commands are spelled `unique%` / `schema%` / `typed%` / `cascade%` so
`unique` stays an identifier (`IndexSpec.unique`) and `schema` stays a
definition name (`withDb path schema`).

**State.** `Table α` is the AUTOINCREMENT counter and rows in id order
(child lists attached). `DbState s` has one table per entity of `s`.
`DbState.load` reads every table under one `readSnapshot`. `DbState.WF`
is `checkWF = true`: every row decodes and is `Checked`, ids strictly
increase and stay `< next`, unique keys are unique, foreign keys
resolve, child lists attach. `checkWF` is decidable; proofs that writes
preserve `WF` are M15.

**Queries.** `Query s ts ρ` is a `Pred` over tables `ts`, typed `OrderKey`s
that finish with the id tiebreak, and a `Window`. `Query.from`, `where'`,
`orderBy`, `withWindow`, `join` along a declared foreign key. Meaning is
`selectSpec` then `Window.apply`. A window, `first`, `count`, `exists`,
or `page` requires an exact plan (`exact_plan` as the default for
`_h : q.exact = true`); unwindowed `all` may keep a Lean residual. FK
`join` is an `eq2` of the fk column against the target id (SQL `JOIN`),
so it is exact and windows/counts go to SQL.

**Reads.** `Read s α` has `get`, `lookup`, `first`, `all`, `page`, `count`,
`exists` (as `Read.exists` / `Read.exists'`), `pure`/`bind`. No write
constructor and no failure channel. `Read.denote` is total on a
well-formed state. `Read.run` executes in one deferred snapshot and
returns `Except DbFault α`. `Runtime.Service.runRead` uses a reader
connection (`withReader`); `runTxn` uses the writer under
`BEGIN IMMEDIATE`.

**Faults.** `DbFault` is locking, I/O, corruption/undecodable row, or
schema mismatch. These are not part of a `Read` or `Txn` type.

## Part B

**Failure types**, derived from the schema:

- `InsertError α` — `duplicate ix holder`, `missingRef fk`
- `UpdateError α` — `stale current`, `gone`, then the insert failures
- `SetError α fs` — `gone`, `duplicate` on `Unique.Touching fs`,
  `missingRef` on `ForeignKey.Within fs` (only constraints over written
  fields; each is `Empty` when none overlap, so an exhaustive `match`
  may omit the constructor and `IsEmpty` is found)
- `AppendError α` — `stale current`, `gone`, `notAppend list`
- `DeleteError s α` — `gone`, `restricted` on `ReferencedBy.Restricting`
  (cascading inbound keys do not inhabit `restricted`)

Absent failures are uninhabited (`Unique α := Empty` with no index, and
the same for `ForeignKey` / `ListField` / `ReferencedBy`, and for
`Restricting` when every inbound key cascades). `IsEmpty` is found
automatically; `insertNew` requires `[IsEmpty (InsertError α)]`.

**Programs.** `Txn σ s ε α` reads and writes over schema `s` and may abort
with `ε`. `σ` is an ST-style transaction index: `Current σ α` is a row
this transaction has seen, coerces to `Stored α`, and cannot leave
`Txn.run` (`{σ : Type} → Txn σ s ε α`). `Read` embeds. Combinators:
`throw`, `orAbort`, `orElse`. Writes take `Checked α`:

| Operation | Failure | Success |
|---|---|---|
| `insert` | `InsertError α` | `Current σ α` |
| `insertNew` | (none; needs `IsEmpty`) | `Current σ α` |
| `update` | `UpdateError α` | `Stored α` (CAS, `IS` on parent columns) |
| `set` | `SetError α Fields.all` | `Current σ α` |
| `patch` | `SetError α fs` | `Current σ α` (SQL `UPDATE` of `fs` only) |
| `append` | `AppendError α` | `Stored α` |
| `delete` | `DeleteError s α` | `Stored α` (RESTRICT or CASCADE per key) |

**Meaning.** `Txn.denote : Txn σ s ε α → DbState s → Except ε α × DbState s`.
Id assignment uses the per-table AUTOINCREMENT counter. Unique indexes
are checked in declaration order, then foreign keys in field order;
`delete` counts restricting inbound keys (not cascading ones) in schema
then field order, then removes cascade-referencing rows. An abort
(`throw` / `orAbort`) returns the original state.

**Execution.** `Txn.run` is `BEGIN IMMEDIATE`, a SAVEPOINT around each
write (`withTransaction`), and the same constraint checks in the same
order before the statement. It returns `Except DbFault (Except ε α)`.
A domain abort rolls back the outer transaction.

**Harness.** `LeanDb/Typed/Harness.lean` compares `run` to `denote` on
answer, failure constructor with payload, and final tables, and asserts
`checkWF` after every successful load, denote, and load-after.
`TestsM14b.lean` uses the part A schema (join, child list, unique
indexes, foreign key, invariant), ports the QUERIES.md §3.6 `register`
and `deleteTeam` examples, and includes a `#guard_msgs` test that adding
`unique Account2.byEmail` makes a non-exhaustive `InsertError` match
fail.

## Part C

Gaps against QUERIES.md §3 / §5, closed on this branch.

**`patch` writes only the named fields.** Meaning merges with
`Fields.apply fs old new`: the stored row keeps every column not in
`fs`, including child lists (they are not `Entity.Field`s). Execution
`UPDATE`s only those columns (`Fields.toEnginePatch`). Callers still
pass a `Checked α` of a full row rather than a `{ f := v, … }` literal:
the merged row is then `Checked` whenever the invariant does not mix a
written field with an unwritten one (the usual case, e.g. `User.invariant`
is `name ≠ ""` and a patch of `email` keeps `name`). A `Patch α fs`
value plus a post-merge `check` would re-introduce an invariant failure
on the write, which QUERIES.md forbids. Callers typically write
`{old with f := v}`, so merge equals `new`.

**Filtered constraint types.** `Unique.Touching fs` and
`ForeignKey.Within fs` are `if any overlap then subtype else Empty`.
`ReferencedBy.Restricting` is the same for restrict inbound keys
(`anyRestrict` is a Boolean literal on the generated instance). A patch
that writes no `Ref` has uninhabited `missingRef`; a delete whose only
inbound keys cascade omits `restricted`. Exhaustive `match` may skip
those constructors; `IsEmpty` is found automatically.

**Exactness.** `withWindow` / `Read.first` / `count` / `exists` / `page`
take `_h : q.exact = true := by exact_plan`. The tactic fails with a
clear error when the plan has an opaque leaf. Unwindowed `Read.all` may
keep a residual. FK `join` pushes `FROM t0 JOIN t1 ON <eq2>`.

**`runRead` / `runTxn`.** `Runtime.Service.runRead` runs on
`withReader` (refuses a writable conn) in one deferred snapshot.
`runTxn` runs on the writer under `BEGIN IMMEDIATE`.

**Declared delete.** Per foreign key: RESTRICT (default) or CASCADE via
`cascade%` before derive. Mirrored in SQLite `ON DELETE`, in
`deleteCascading`, and in `DeleteError` (`Restricting`, not every
`ReferencedBy`).

## Remaining deviations

Relative to QUERIES.md §3 / §5. Not silently weakened.

- **`where'` is a `Pred`, not a Lean predicate refused unless exact.**
  Unwindowed `all` may keep `.opaque`. Exactness is demanded only where
  a window or aggregate would otherwise be unsound.
- **`patch` is `fs` plus a full `Checked α`**, not a field-literal
  syntax. See Part C.
- **`JoinCol α β` is keyed on the pair of entity types.** Two `Ref`
  fields from `α` to the same `β` would overlap instances. `join` still
  takes a `ForeignKey`, but SQL uses that unique instance.
- **`q.exact = true` is not always `rfl`.** `exact_plan` tries `rfl`
  then `native_decide` (joins through `JoinCol` do not unfold enough
  for definitional equality).
- **Cascade of a restrict victim is not in `DeleteError`.**
  `restricted` lists inbound keys of the deleted row only. If a cascade
  victim is itself restrict-referenced, SQLite fails the statement (a
  `DbFault`); the meaning still removes the cascade victims. Nested
  restrict-on-cascade is not typed. `deleteCascading` is `partial`
  (recursion over heterogeneous `Source` types).
- **`Touching` / `Within` / `Restricting` are `if`/`Empty`, not
  generated inductives.** They reduce to `Empty` when nothing applies,
  which is what exhaustive match and `IsEmpty` need in Lean 4.33.
- **WF preservation is unproved.** `checkWF` holds in the harness after
  every successful write and program; the proofs are M15 (QUERIES.md
  §3.10).
- Command names keep the `%` suffix (`unique%`, `schema%`, `cascade%`)
  so they do not collide with existing identifiers.
