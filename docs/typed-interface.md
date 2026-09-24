# Typed interface (M14)

LeanDB programs as values: a read has a pure meaning over `DbState`, and
execution is one deferred snapshot. Writes and transaction programs are
M14 part B.

## Part A (this milestone)

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
schema mismatch. These are not part of a `Read` type.

## Part B (next)

Writes as values, each with a failure type derived from the schema
(`InsertError`, `UpdateError`, `SetError`, `AppendError`, `DeleteError`):
unique clashes, missing refs, stale CAS, restrict-on-delete. Writes take
`Checked α`. `Txn s ε α` declares its failure type, is all-or-nothing
(`throw`, `orAbort`, `orElse`), and runs under `BEGIN IMMEDIATE` with a
SAVEPOINT per write. `Current α` is a row this transaction has seen
(`set`/`patch` have no `stale`). `Read` embeds into `Txn`. The
execution-equals-meaning harness (random well-formed states against
SQLite and `denote`) ships with part B.
