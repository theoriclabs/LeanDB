# Typed interface (M14 / M15-pre / M15a)

LeanDB programs as values: a read has a pure meaning over `DbState`, and
execution is one deferred snapshot. Writes and transaction programs have
the same shape: a failure type derived from the schema, a pure meaning,
and `run` that equals that meaning on well-formed states. The kernel
sees the same `DbState` the compiled code runs.

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
- `Valid α` is a stored row plus `Invariant α stored.val`. `Read.get` /
  `lookup` / `first` / `all` / `page` return `Valid α` (joins
  `Valid α × Valid β`). Coerces to `Stored α`, so `Query.from` /
  `where'` / `orderBy` still see `Stored α`.

Commands are spelled `unique%` / `schema%` / `typed%` / `cascade%` so
`unique` stays an identifier (`IndexSpec.unique`) and `schema` stays a
definition name (`withDb path schema`).

**State.** `Table α` is the AUTOINCREMENT counter and rows in id order
(child lists attached). `IsSchema s` is `nTables : Nat` and
`pack : Fin nTables → PackedEntity`. `schema%` generates a named
`S.instIsSchema` (so `Has.id` is a concrete `Fin n`, e.g. `Fin 2`, and
`decide` never sees a free `i.nTables`) plus `instance : IsSchema S :=
S.instIsSchema`. Tables are `Fin nTables` rather than a generated
inductive `i.Table`: `Fin` already has `DecidableEq`, lives in `Type`,
and `Has.id` is a numeral the kernel can compute.

```
structure DbState (s) [i : IsSchema s] where
  tables : (t : Fin i.nTables) → Table (i.pack t).ty
```

The Pi lives in `Type` because each `Table _` does, so `DbState s` is a
`DbM` result. There is no `unsafe` / `implemented_by` in `LeanDb/Typed`:
the logical body is the executed one. `Table.rows` is `List (Valid α)`:
the invariant proof is stored with the row (by construction). `get` /
`set` transport `Table` along `IsSchema.Has.ty_eq` using
`Has.entity_eq` (generated `rfl`), so `Valid` does not need a separate
`Eq.rec` motive.

- `get` transports `st.tables h.id` along `IsSchema.Has.ty_eq`.
- `set` is function update (`if t = h.id then transport tbl else st.tables t`).
- `load` reads every table in id order under one `readSnapshot` (`fetchAll`
  plus `sqlite_sequence`).
- `getSource` / `snapshot` are defined on top of that Pi (`getSource`
  transports along `sourceTy_eq`; `snapshot` folds `st.tables t`).
- Proved, no `sorry`: `get_set_same`, `get_set_other`, `empty_rows`,
  `empty_next`. Non-vacuity: `TestsM14a.insert_team_on_empty` — `denote
  (insert v) empty` has exactly one Team row, `v` (`simp` / `rfl`, no
  `native_decide`).
- `DbState.WF` is `checkWF = true`. `checkWF` is decidable; proofs that
  writes preserve `WF` remain M15.

**Queries.** `Query s ts ρ` is a `Pred` over tables `ts`, typed `OrderKey`s
that finish with the id tiebreak, and a `Window`. `Query.from`, `where'`,
`orderBy`, `withWindow`, `join` along a declared foreign key. Meaning is
`selectSpec` then `Window.apply`, gathering rows via `GatherState` (each
position is `DbState.get`). A window, `first`, `count`, `exists`, or
`page` requires an exact plan (`exact_plan` as the default for
`_h : q.exact = true`); unwindowed `all` may keep a Lean residual. FK
`join` is an `eq2` of the fk column against the target id (SQL `JOIN`).
`exact_plan` is `rfl | (dsimp; rfl) | decide`. Joins through `JoinCol`
often need an explicit `Exact` proof (see deviations).

**Reads.** `Read s α` has `get`, `lookup`, `first`, `all`, `page`, `count`,
`exists` (as `Read.exists` / `Read.exists'`), `pure`/`bind`. No write
constructor and no failure channel. `Read.get` / `lookup` return
`Option (Valid α)` from the table (by construction). `first` / `all` /
`page` wrap the query's `ρ` through `QueryRow`: a from-query answers
`Valid α`, a join `Valid α × Valid β`. Meaning looks the gathered
`Stored` row up in `Table.rows`; execution uses `Valid.ofStoredM`
(decode-time invariant failure is `DbFault.corruption`, never a
returned row). `Valid` coerces to `Stored α`. `Query.from` still
answers `Stored α`, so `where'` / `orderBy` are unchanged.
`Read.denote` is total on a well-formed state. `Read.run` executes in
one deferred snapshot and returns `Except DbFault α`.
`Runtime.Service.runRead` uses a reader connection (`withReader`);
`runTxn` uses the writer under `BEGIN IMMEDIATE`.

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
this transaction has seen, carries `property : Invariant α stored.val`,
coerces to `Stored α` and `Valid α`, and cannot leave `Txn.run`
(`{σ : Type} → Txn σ s ε α`). `Read` embeds. Combinators: `throw`,
`orAbort`, `orElse`. Writes take `Checked α`. `update` / `append` take
a `Valid α` current row plus a proof-built `Checked` new value (no
runtime re-check of the old row). `set` / `patch` take `Current σ α`.

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
answer, failure constructor with payload, and final tables via lawful
`get` (`getEq` / `tableEq` on ids and values — not a placeholder empty
table). `checkWF` after every successful load, denote, and load-after.
Random programs in `TestsM14b.lean` use the same structural compare.
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
is `name ≠ ""` and a patch of `email` keeps `name`). If the merge *does*
break the invariant, both meaning and execution return
`SetError.invalid` (never a `DbFault`). Callers typically write
`{old with f := v}`, so merge equals `new`.

**Filtered constraint types.** `Unique.Touching fs` and
`ForeignKey.Within fs` are `if any overlap then subtype else Empty`.
`ReferencedBy.Restricting` is the same for restrict inbound keys
(`anyRestrict` is a Boolean literal on the generated instance). A patch
that writes no `Ref` has uninhabited `missingRef`; a delete whose only
inbound keys cascade omits `restricted`. Exhaustive `match` may skip
those constructors; `IsEmpty` is found automatically.

**Exactness.** `withWindow` / `Read.first` / `count` / `exists` / `page`
take `_h : q.exact = true := by exact_plan`. The tactic is
`rfl | (dsimp; rfl) | decide` (no `native_decide`). It fails with a
clear error when the plan has an opaque leaf, or when `decide` cannot
close `q.exact = true`; then pass an explicit proof. Unwindowed
`Read.all` may keep a residual. FK `join` pushes `FROM t0 JOIN t1 ON
<eq2>`.

**`runRead` / `runTxn`.** `Runtime.Service.runRead` runs on
`withReader` (refuses a writable conn) in one deferred snapshot.
`runTxn` runs on the writer under `BEGIN IMMEDIATE`.

**Declared delete.** Per foreign key: RESTRICT (default) or CASCADE via
`cascade%` before derive. Mirrored in SQLite `ON DELETE`, in
`deleteCascading`, and in `DeleteError` (`Restricting`, not every
`ReferencedBy`). `deleteAt` is fueled by `DbState.rowCount` (not
`partial`). The current row is erased *before* the recursive walk, so
each row is deleted at most once and a cycle cannot re-enter it.
Recursion depth on remaining rows is ≤ the starting `rowCount`. The
fuel-0 branch is totality only, not a distinct SQLite fallback.

## M15-pre

**Axiom check.** `scripts/CheckAxioms.lean` (`#check_m15_axioms`) prints
axioms of `DbState.get_set_same`, `get_set_other`, `empty_rows`,
`Txn.denote`, `Read.denote`, and `TestsM14a.insert_team_on_empty`, and
fails if anything beyond `propext`, `Classical.choice`, `Quot.sound`
appears. Imported from `Tests.lean`, so `lake exe leandb_tests` runs it.

**LeanAPI migration** (`examples/**/DbApi.lean`, e.g. private-games
`writeStep`). Do not re-check `GameRow.invariant s.val` after a typed
read. Point reads *and* `Read.first` / `all` / `page` carry the proof:

- `Read.get` / `lookup` : `Option (Stored α)` → `Option (Valid α)`
  (still coerces to `Stored α`).
- `Read.first` / `all` / `page` of a from-query: `Option (Valid α)` /
  `List (Valid α)` / `Page (Valid α)` (joins `Valid α × Valid β`).
- `Txn.get` / `lookup` : `Option (Current σ α)` with `property`.
- `Txn.update` / `append` take `Valid α` (not `Stored α`) plus `Checked`.
- Delete the `if hv : GameRow.invariant s.val = true then … else
  unreachable` around `writeStep`. `visibleGame` already uses
  `Read.first`; its row is `Valid GameRow`. Pass that `s` (or
  `Current.toValid`) and use `s.property` in `GameRow.checkedStep`.
  `TestsM14c.writeEmail` is the compiling pattern.

## M15a

Meaning and execution agree on the findings a review listed as D1–D10
(and on stale `BEq` payloads and issued-id positivity). Each fix has a
regression in `TestsM15a.lean`. `LeanDb.ExecutesAsMeaning s` is the
named `Prop` LeanAPI takes as a hypothesis (LAPI-06): for every program
and every well-formed loaded state, a `run` that completes without a
`DbFault` has the same answer, typed-failure payload, and tables as
`denote`. It is **not** an `axiom` and is **not** proved (it is about
SQLite). The evidence is the M15a harness: 572 fixed-seed cases over a
schema with child lists, a nullable `Ref`, a closed enum in `orderBy`,
a two-level cascade, a restrict key, unique indexes and foreign keys;
random `insert` / `update` / `set` / `patch` / `append` / `delete` /
`orElse` / `throw` and reads inside a `Txn` after writes; states of up
to about 30 rows per table; `checkWF` before and after.

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
- **`q.exact = true` is not always `rfl`.** `exact_plan` tries `rfl`,
  `dsimp; rfl`, then `decide`. Joins through `JoinCol` often do not
  unfold enough for `decide`; those call sites pass an explicit proof
  (e.g. `withTeam_exact` in `TestsM14a.lean`).
- **Cascade of a restrict victim is not in `DeleteError`.**
  `restricted` lists inbound keys of the deleted row only. If a cascade
  victim is itself restrict-referenced, SQLite fails the statement (a
  `DbFault`); the meaning still removes the cascade victims. Nested
  restrict-on-cascade is not typed. `deleteAt` erases before walking;
  fuel = `rowCount` suffices because each row is deleted at most once
  (a cycle cannot re-enter a gone id). Lean cannot inhabit a cyclic
  `Ref` on a structure (nested occurrence), so there is no derived
  cyclic-DDL fixture; the bound is the agreement with SQLite CASCADE.
- **`Query.from` answers `Stored α`, not `Valid α`.** Filters and
  ordering stay over `Stored` (`Valid` coerces). `Read.first` / `all` /
  `page` wrap through `QueryRow` to `Valid α` (joins `Valid α × Valid β`).
- **Tables store `Valid α`.** The proof is by construction (`Table.cast`
  along `ty_eq` / `entity_eq`). Execution still refuses a decode-time
  invariant failure as `DbFault.corruption`.
- **`Touching` / `Within` / `Restricting` are `if`/`Empty`, not
  generated inductives.** They reduce to `Empty` when nothing applies,
  which is what exhaustive match and `IsEmpty` need in Lean 4.33.
- **WF preservation is unproved.** `checkWF` holds in the harness after
  every successful write and program; the proofs are later (QUERIES.md
  §3.10). `ExecutesAsMeaning` is the named hypothesis for the SQLite
  half; it is not an axiom.
- **`Ref` inside a child-list record is refused at `schema%` / `typed%`.**
  SQLite would enforce those FKs; the typed `ForeignKey` layer would
  not. Put the reference on a schema table.
- **`Id α` / `Ref α` still admit any `Int64`.** Issued ids are ≥ 1
  (`Table.idsOk`, `Table.refsOk`, AUTOINCREMENT). Use `Id.toNat` for
  the `Nat` of an issued id (`Id.toNat_one`); apps no longer need a
  non-negativity hypothesis under `checkWF`.
- **`Entity.rangeOk` (folded into `Invariant` / `Checked`) is generated
  for `Nat` / `Option Nat` columns.** Other codecs that override
  `toSql?` to refuse values, and `Nat`s only in child-list records, are
  not in that conjunction. Custom refusing codecs should be listed as
  `canRefuse` in the derive walk if they appear.
- **A quantifier nested three joins deep becomes `.tt` under
  `Pred.extendUnder3`.** Child lists are one level, so D9 (quantifier
  then one `join`) keeps its body. A three-table join after a nested
  `exists`/`forall` would drop that inner filter in the meaning; refuse
  that shape or extend the walk if a schema needs it.
- Command names keep the `%` suffix (`unique%`, `schema%`, `cascade%`)
  so they do not collide with existing identifiers.
