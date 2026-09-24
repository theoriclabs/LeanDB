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
- `Checked α := { v : α // Invariant α v }`, built by `Entity.check` /
  `Checked.check` at runtime or `Checked.of` from a proof.

Commands are spelled `unique%` / `schema%` / `typed%` so `unique` stays
an identifier (`IndexSpec.unique`) and `schema` stays a definition name
(`withDb path schema`).

**State.** `Table α` is the AUTOINCREMENT counter and rows in id order
(child lists attached). `DbState s` has one table per entity of `s`.
`DbState.load` reads every table under one `readSnapshot`. `DbState.WF`
is the per-state well-formedness predicate (ids and invariants here;
unique/FK closure is an M15 law).

**Queries.** `Query s ts ρ` is a `Pred` over tables `ts`, typed `OrderKey`s
that finish with the id tiebreak, and a `Window`. `Query.from`, `where'`,
`orderBy`, `withWindow`, `join` along a declared foreign key. Meaning is
`selectSpec` then `Window.apply`. SQL pushes LIMIT/OFFSET/COUNT/EXISTS
only when the plan is exact (`!pred.hasOpaque`).

**Reads.** `Read s α` has `get`, `lookup`, `first`, `all`, `page`, `count`,
`exists` (as `Read.exists` / `Read.exists'`), `pure`/`bind`. No write
constructor and no failure channel. `Read.denote` is total on a
well-formed state. `Read.run` executes in one deferred snapshot and
returns `Except DbFault α`.

**Faults.** `DbFault` is locking, I/O, corruption/undecodable row, or
schema mismatch. These are not part of a `Read` or `Txn` type.

## Part B

**Failure types**, derived from the schema:

- `InsertError α` — `duplicate ix holder`, `missingRef fk`
- `UpdateError α` — `stale current`, `gone`, then the insert failures
- `SetError α fs` — `gone`, `duplicate` on `Unique.Touching fs`,
  `missingRef` on `ForeignKey.Within fs` (only constraints over written
  fields)
- `AppendError α` — `stale current`, `gone`, `notAppend list`
- `DeleteError s α` — `gone`, `restricted who rows`

Absent failures are uninhabited (`Unique α := Empty` with no index, and
the same for `ForeignKey` / `ListField` / `ReferencedBy`). `IsEmpty` is
found automatically; `insertNew` requires `[IsEmpty (InsertError α)]`.

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
| `patch` | `SetError α fs` | `Current σ α` |
| `append` | `AppendError α` | `Stored α` |
| `delete` | `DeleteError s α` | `Stored α` |

**Meaning.** `Txn.denote : Txn σ s ε α → DbState s → Except ε α × DbState s`.
Id assignment uses the per-table AUTOINCREMENT counter. Unique indexes
are checked in declaration order, then foreign keys in field order;
`delete` counts inbound references in schema then field order. An abort
(`throw` / `orAbort`) returns the original state.

**Execution.** `Txn.run` is `BEGIN IMMEDIATE`, a SAVEPOINT around each
write (`withTransaction`), and the same constraint checks in the same
order before the statement. It returns `Except DbFault (Except ε α)`.
A domain abort rolls back the outer transaction.

**Harness.** `LeanDb/Typed/Harness.lean` compares `run` to `denote` on
answer, failure constructor with payload, and final tables.
`TestsM14b.lean` uses the part A schema (join, child list, unique
indexes, foreign key, invariant), ports the QUERIES.md §3.6 `register`
and `deleteTeam` examples, and includes a `#guard_msgs` test that adding
`unique Account2.byEmail` makes a non-exhaustive `InsertError` match
fail.
