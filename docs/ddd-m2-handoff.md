# DDD milestone 2: LeanDB wave 1 (native half)

Scope: DDD-LDB-07 (schema changes wait for a migration), the native support for
the post's entity-based RSVP (DDD-LDB-05/06 native parts), and what wave 2 needs
from the portable layer. Everything is uncommitted, in LeanDB only. Lean 4.33.0,
`LEAN_NUM_THREADS=2`. `CHANGELOG.md`, `docs/roadmap.md` and
`docs/typed-interface.md` are byte-identical to the baseline (SHA-256 below).
`members%`, `Read.memberField`, `Read.discloseWith` and `MemberHandle` are
unchanged and still tested.

## What landed

### A. DDD-LDB-07: the migration gate

**What happens today (investigated before implementing).** A database created
with `Party { host, title, description, date }`, then opened with the post's
`Party` that adds `guestList : GuestListVisibility` (required, no default):

1. `openDb` (which `DbConns.open` and `app% serve` call) refuses with
   `[schema_mismatch] schema fingerprint mismatch: code has 15922890394775669303,
   instance has 14520308419256641563`. It names no table or field. The served
   Partiful binary exits with `open partiful.db: <that message>`. It has no
   migrate entry point.
2. `migrate` (plan only) refuses with `table "party": new column "guestList" is
   NOT NULL with no default …`. It names only the first such column, and the app
   cannot reach it.
3. With a structure default (`guestList := .everyone`), `migrate` would plan
   `add column "party"."guestList"`, a DDL `DEFAULT`. So the value lived in the
   type, not in a migration. The M1 Partiful domain's `visibility := .public` is
   this case. `openDb` still refuses until something runs `migrate`.

`TestsDddM2` asserts behavior 1 as a baseline before it exercises the gate.

**The gate** is in `LeanDb/Typed/Gate.lean`. It reuses the existing engine:
`planMigration`, `Migration.applyOn` (its transaction, journal, PRAGMA
restore and backup), the fingerprints, the stored `schema_json`, and
`canonicalizationPreflight`.

- It compares the compiled fingerprint with the stored one. If they are equal,
  the status is `upToDate`. If no schema is recorded, the status is `fresh` and
  `Conn.verify` creates the tables.
- If they differ, it classifies each difference against the stored schema. The
  gate makes a change on its own only when no data is invented or
  reinterpreted: a new table, an optional or defaulted column, a grown closed
  world, a changed default or delete action, required→optional, a new non-unique
  index, or a dropped index. A new required field needs a declared fill. A
  dropped field or table, or a retyped, shrunk, re-referenced or
  optional→required field, is refused. The refusal names `Entity.field (table,
  column)` for every finding, not just the first.
- A new unique index (declared, or arising from new code) is preflighted on the
  stored rows, with the post-migration values: stored columns, the fill, the
  default or NULL. It uses the index's collation and partial `WHERE`, and NULL
  never collides, as in SQLite. Every colliding group is reported with its key
  and all row ids. No survivor is picked and nothing is applied.
- A covered change is applied by `Migration.applyOn` in one transaction:
  1. typed fill rewrites (`Step.transform`)
  2. the mechanical steps
  3. index creation
  4. `foreign_key_check`
  5. the new fingerprint, schema and version
  6. the `_leandb_migrations` journal entry
  7. one `_leandb_applied_migrations` row per declared migration used

  All of these commit together or not at all.
- `Gate.command?` gives the app executable `migrate --check` (read-only) and
  `migrate`. `Gate.ensure` / `Gate.openDb` are the startup gate.

Migrations are ordinary Lean values. The fill has the field's type, so
`(fill := "everyone")` is a compile error, checked by a fixture:

```lean
def addGuestList := SchemaMigration.addField Party Party.Field.guestList (fill := .everyone)
-- or, as the post spells it, recorded under its own name:
migration% addGuestList := Party.addField guestList (fill := .everyone)
migration% emailsCanonical := Person.checkCanonical email Email.parse
```

`migration%` is a command, not a generated constant. `T.addField f (fill := v)`
resolves `f` through `Entity.Field T`, so it also works on bridge entities,
whose symbols are `T.DbField`. An unknown field is rejected by name. An
author-defined `T.addField` is used as written.

**Two pre-existing engine bugs found and fixed** (both are mutation-tested: with
the fix removed, the new test fails):

- A table rebuild (`MigStep.rebuildTable` SQL, and `transformTable` for
  `Step.transform`) reset the AUTOINCREMENT counter to `max(id)`. Ids of deleted
  newest rows were then handed out again. `carrySequenceSql` now carries the
  counter across the swap.
- `Migration.applyOn` with a `transform` created the new table without its
  indexes. They only came back at the next `verify`, after commit, so a unique
  index the rewritten rows violate failed after the migration had committed.
  The indexes are now created inside the migration transaction.

### B. The post's entity-based RSVP, natively

Natively the post's declarations are:

```lean
structure Rsvp where
  party : Ref Party
  guest : Ref Person
cascade% Rsvp.party                         -- decision 8; Rsvp.guest restricts
deriving instance LeanDb.Entity for Rsvp
unique% Rsvp.onePerGuest := (party, guest)
```

- **Composite unique.** This already existed natively. The typed alternative is
  `Rsvp.Unique.onePerGuest`, and its exact identity is the physical index
  `uq_rsvp_onePerGuest`, through both `Unique.identity` and `Unique.metadata`.
  For natively declared uniques, `EntityStorage.sourceUnique` defaults to
  `Unique.identity`. Single-field portable uniques keep their generated
  mapping.
- **Typed conflict.** `Txn.insertUnique` fails only with the declared unique
  alternatives, carrying no holder. A missing reference aborts the transaction
  with a mapped error, so foreign-key failures are not conflicts. A duplicate
  leaves every table and counter unchanged; the law is
  `Txn.insertUnique_duplicate`. The post's `rsvp` match without
  `.error .onePerGuest` is rejected with
  `Missing cases: (Except.error Rsvp.Unique.onePerGuest)`.
- **Unique lookup.** `Read.findBy` (= `Read.lookup`) and `Txn.lookup` work for
  single and composite keys. `Read.lookupSql` returns the exact statement the
  executor prepares (`fetchFiltered` now builds its SQL through
  `filteredSelectSql`; the bytes are identical). `EXPLAIN QUERY PLAN` shows
  `INDEX uq_person_uniqueEmail (email=?)` and
  `INDEX uq_rsvp_onePerGuest (party=? AND guest=?)`.
- **Cascade.** Ordinary-entity foreign keys already supported
  `cascade%` + `Txn.delete`, in both the meaning and SQLite. No change was
  needed. Tests:
  - cancelling a party deletes only its RSVPs
  - people and counters stay
  - a guest with RSVPs is `restricted` (`rsvp.foreignKey.guest`, 2 rows)
  - `cancel`'s `restricted` branch is `nomatch` (statically empty)

  `Derive.declareCascade` is the programmatic form, so wave 2's
  `native_schema%` can carry a portable `onDelete := cascade`.
- **Typed semi-join projection.** `LinkRelation p t e` is plain data: two field
  symbols and two getters, plus coherence laws that are `rfl` when written from
  the same field. A swapped column is rejected by a fixture. The new read is
  `Read.linkField`:

  ```sql
  SELECT t."name" FROM "person" AS t
  WHERE t.id IN (SELECT e."guest" FROM "rsvp" AS e WHERE e."party" = ?)
  ORDER BY t.id ASC
  ```

  It selects the name only, each target once, in guest-id order. The plan is
  `COVERING INDEX uq_rsvp_onePerGuest (party=?)` plus `INTEGER PRIMARY KEY`
  lookups, with no scan. It runs with emails corrupted to a BLOB, so no
  hydration happens. The provenance law is `Read.linkField_provenance`. The
  `IN` form equals the meaning on any state, with no uniqueness assumption.
- **Denial wrapper.** `Read.discloseIf allowed (projection : allowed → Read s α)
  visible hidden`. When the proof is absent, the program *is* `pure hidden`.
  The law is `Read.discloseIf_denied`, an equality of programs, so nothing is
  prepared. The test drops `rsvp`: denial still succeeds, and the allowed read
  faults. Calling the post's `exportGuests` without the proof is rejected with
  the post's `… → Read S (List String)` type mismatch.
- **`Party.Changes` needs no new native support.** An edit is
  `Txn.patch Party row (Fields.of [title, description, guestList]) checked`.
  `Fields.apply` writes only those columns: a full row carrying another host and
  date writes neither (tested). The failure type has no `duplicate` or
  `missingRef` alternative (both are `nomatch`), because no editable field has
  a unique or a reference. Deriving the `Changes` structure and lens is
  portable work.

### Wave 1.5: foreign-key access paths

Every reference column that no declared full (non-partial) index leads now gets
an engine-owned index, `_leandb_fk_<table>_<column>`
(`TableSpec.fkIndexDdl`). For the post's schema that means `Rsvp.guest` and
`Party.host`; `Rsvp.party` is already led by `uq_rsvp_onePerGuest`, and
`members%` edges and child tables are already led by their pair indexes. The
index serves:

- the executor's restrict count for a delete (`ReferencedBy.countSql`)
- SQLite's own `ON DELETE` CASCADE/RESTRICT enforcement
- reverse lookups

**Decision (gate).** These indexes are *derived, not declared*: they are not in
`TableSpec.indexes`, `fullDdl` or the fingerprint. They carry no data and
change no answer, so they are never schema drift. They are applied
automatically and safely:

- `Conn.verify` runs `CREATE INDEX IF NOT EXISTS` on every writer open, plus a
  `DROP INDEX IF EXISTS` once a declared index starts leading the column.
- `MigStep.createTable`/`rebuildTable` and the transform rebuild create them
  inside the migration transaction.

An existing database therefore gains them on its next open with no migration.
`Gate.check` reports `upToDate`, not a finding, and every existing fingerprint
and frozen migration chain stays valid. The alternative, declaring them in the
spec, would have changed the fingerprint of every existing schema with a
reference, so plain `openDb` would refuse those databases. Supporting changes:

- `validateSchema` now refuses declared index names with the reserved
  `_leandb_` prefix.
- The importer skips `_leandb_*` indexes.

**Tests (`EXPLAIN QUERY PLAN`).**

- Deleting a person with RSVPs: both restrict counts use
  `COVERING INDEX _leandb_fk_party_host (host=?)` and
  `_leandb_fk_rsvp_guest (guest=?)`, with no scan. The delete is still
  `restricted rsvp.foreignKey.guest 2`, and it matches the meaning.
- Cancelling a party: the cascade statement SQLite runs
  (`DELETE FROM "rsvp" WHERE "party" = ?`, `ReferencedBy.cascadeSql`) uses
  `COVERING INDEX uq_rsvp_onePerGuest (party=?)`.
- An existing database without the index: after `DROP INDEX`, the count plan
  is `SCAN rsvp`; `Gate.check` gives `upToDate`; `Gate.openDb` recreates the
  index (fresh plan uses it); and rows and counters are unchanged.
- After the gate migrates V1 → current (with the `party` rewrite), both FK
  indexes exist.

## Interface for peers (exact native signatures)

Migration gate (`LeanDb.Typed.Gate`):

```lean
structure LeanDb.SchemaMigration where
  name : String
  changes : List SchemaMigration.Change
def LeanDb.SchemaMigration.addField (α : Type) [Entity α] (field : Entity.Field α)
    (fill : Entity.fieldTy field) : SchemaMigration
def LeanDb.SchemaMigration.checkCanonical (α : Type) [Entity α] (field : Entity.Field α)
    {κ : Type} [BEq κ] (parse : String → Except String κ) : SchemaMigration
-- command: migration% <name> := T.addField f (fill := v) | T.checkCanonical f parse | <SchemaMigration term>
structure LeanDb.Gate.Target where
  specs : List TableSpec
  entityOf : String → Option String := fun _ => none
def LeanDb.Gate.Target.ofSchema (s : Type) [IsSchema s] : Gate.Target
inductive LeanDb.Gate.Status | fresh | upToDate | pending (plan : Plan) | refused (findings : List Finding)
inductive LeanDb.Gate.Finding
  | missingFill (entity table column : String) | unsupported (subject why : String)
  | duplicates (entity table index : String) (columns : Array String) (groups : List DuplicateGroup)
  | preflight (migration subject : String) (problems : List String) | unreadable (why : String)
inductive LeanDb.Gate.Outcome | fresh | upToDate | applied (plan : Plan) (report : MigrateReport)
structure LeanDb.Gate.Options where
  preflight : Bool := true
  backup : Option System.FilePath := none
def LeanDb.Gate.check (conn : Conn) (target : Target) (migrations : List SchemaMigration)
    (opts : Options := {}) : IO (Except DbError Status)                      -- read-only
def LeanDb.Gate.apply (conn : Conn) (target : Target) (migrations : List SchemaMigration)
    (opts : Options := {}) : IO (Except DbError Outcome)    -- refusal = .error (.migrate render)
def LeanDb.Gate.openDb (path : System.FilePath) (target : Target) (migrations : List SchemaMigration)
    (opts : Options := {}) : IO (Except DbError (Conn × Outcome))     -- gate, then Conn.verify
def LeanDb.Gate.ensure (path : System.FilePath) (target : Target) (migrations : List SchemaMigration)
    (opts : Options := {}) : IO (Except DbError Outcome)
def LeanDb.Gate.command? (path : System.FilePath) (target : Target) (migrations : List SchemaMigration)
    (args : List String) (opts : Options := {}) : IO (Option UInt32)
def LeanDb.Gate.refusedExit : UInt32 := 3
def LeanDb.Gate.appliedMigrations (conn : Conn) : IO (List String)
def LeanDb.Gate.Status.render : Status → String
def LeanDb.readStoredSchemaChecked (conn : Conn) : IO (Except String (Option (List TableSpec)))
def LeanDb.carrySequenceSql (old tmp : String) : List String
```

Foreign-key access paths (wave 1.5):

```lean
def LeanDb.TableSpec.fkIndexName (table column : String) : String     -- "_leandb_fk_<table>_<column>"
def LeanDb.TableSpec.leadsIndex (t : TableSpec) (column : String) : Bool
def LeanDb.TableSpec.fkIndexDdl (t : TableSpec) : Array String         -- not in fullDdl / fingerprint
def LeanDb.TableSpec.fkIndexCleanupDdl (t : TableSpec) : Array String
def LeanDb.ReferencedBy.countSql {s α} [IsSchema s] [HasReferencedBy s α] (r : ReferencedBy s α) : String
def LeanDb.ReferencedBy.cascadeSql {s α} [IsSchema s] [HasReferencedBy s α] (r : ReferencedBy s α) : String
```

`command?` handles `["migrate", "--check"]` and `["migrate"]`, and returns
`none` for any other arguments. `migrate --check` opens the file read-only and
does not create it. It exits 0 when the app would start (up to date, fresh, or a
covered change it will apply), 3 when it would refuse, and 1 on other errors.
The first line of stdout is `status: …`. An app's `main`:

```lean
if let some code ← Gate.command? db (Gate.Target.ofSchema S) migrations args then return code
match ← Gate.ensure db (Gate.Target.ofSchema S) migrations with
| .error e => IO.eprintln e.message; return Gate.refusedExit
| .ok _ => serve …   -- then DbConns.open as today
```

Unique lookup:

```lean
Read.lookup (α : Type) [Entity α] [HasUnique α] [IsSchema.Has s α]
  (ix : Unique α) (key : Unique.Key ix) : Read s (Option (Valid α))          -- existing
abbrev Read.findBy {s} [IsSchema s] (α : Type) [Entity α] [HasUnique α] [IsSchema.Has s α]
  (ix : Unique α) (key : Unique.Key ix) : Read s (Option (Valid α))
Txn.lookup (α : Type) … (ix : Unique α) (key : Unique.Key ix) : Txn σ s ε (Option (Current σ α))  -- existing
def Read.lookupSql {α} [Entity α] [HasUnique α] (ix : Unique α) (key : Unique.Key ix) : String × Array Col
def filteredSelectSql (α : Type) [Entity α] {ts : List Type} (pred : Pred ts)
  (order : Array (Order ts) := #[]) : String × Array Col
```

The composite key is the product in declaration order: `Unique.Key
Rsvp.Unique.onePerGuest = Ref Party × Ref Person`.

Composite unique and typed conflict:

```lean
-- unique% T.name := (f₁, f₂)  →  T.Unique.name, index uq_<table>_<name>
Unique.identity (ix : Unique α) : String                 -- "uq_rsvp_onePerGuest"
Unique.metadata (ix : Unique α) : ConstraintMetadata
def Txn.insertUnique {σ s ε α} [IsSchema s] [Entity α] [HasUnique α] [HasForeignKey α]
    [IsSchema.Has s α] (v : Checked α) (missingRef : ForeignKey α → ε) :
    Txn σ s ε (Except (Unique α) (Current σ α))
theorem Txn.insertUnique_duplicate … (clash : Txn.firstDuplicate v.val st none = some (ix, holder)) :
    Txn.denote (σ := σ) (Txn.insertUnique v missingRef) st = (.ok (.error ix), st)
theorem Txn.insertUnique_missingRef … (noClash : … = none) (missing : Txn.firstMissingRef v.val st = some fk) :
    Txn.denote (σ := σ) (Txn.insertUnique v missingRef) st = (.error (missingRef fk), st)
```

Cascade:

```lean
-- cascade% T.field   (before deriving T)
def LeanDb.Derive.declareCascade (typeName field : Name) : CommandElabM Unit   -- idempotent
Txn.delete (α : Type) [Entity α] [HasReferencedBy s α] [IsSchema.Has s α] (id : Id α) :
  Txn σ s ε (Except (DeleteError s α) (Stored α))                                 -- existing
```

Join projection and denial:

```lean
structure LinkRelation (parent target edge : Type) [Entity parent] [Entity target] [Entity edge] where
  parentField : Entity.Field edge
  targetField : Entity.Field edge
  getParent : edge → Id parent
  getTarget : edge → Id target
  parentColumn : ∀ v : edge, @toCol _ (Entity.codec parentField) (Entity.get parentField v) = toCol (getParent v)
  targetColumn : ∀ v : edge, @toCol _ (Entity.codec targetField) (Entity.get targetField v) = toCol (getTarget v)
Read.linkField {p t e} [Entity p] [Entity t] [Entity e] [IsSchema.Has s e] [IsSchema.Has s t]
  (relation : LinkRelation p t e) (parent : Id p) (field : Entity.Field t) : Read s (List (Entity.fieldTy field))
def Read.linkFieldSql (relation : LinkRelation p t e) (field : Entity.Field t) : String
theorem Read.linkField_provenance … (present : value ∈ Read.denote (.linkField relation parent field) state) :
  ∃ row : Valid t, row ∈ (state.get (α := t)).rows ∧
    (∃ edge : Valid e, edge ∈ (state.get (α := e)).rows ∧
      relation.getParent edge.val = parent ∧ relation.getTarget edge.val = row.id) ∧
    value = Entity.get field row.val
def Read.discloseIf {s α β} [IsSchema s] (allowed : Prop) [Decidable allowed]
  (projection : allowed → Read s α) (visible : α → β) (hidden : β) : Read s β
theorem Read.discloseIf_denied … (denied : ¬ allowed) :
  Read.discloseIf allowed projection visible hidden = .pure hidden
theorem Read.discloseIf_allowed … (granted : allowed) (st) :
  Read.denote (Read.discloseIf …) st = visible (Read.denote (projection granted) st)
theorem Read.discloseIf_denied_equal …   -- denied viewers see the same value on any two states
```

A bridge relation over portable `Ref` fields uses
`getParent := fun r => ReferenceValue.id r.party`, and its laws are still `rfl`
(see `adapters/domain/Tests/GateEvolution.lean`).

## Commands run and results

All runs use the installed Lean 4.33.0 and `LEAN_NUM_THREADS=2`, re-run after the
wave 1.5 change (the last source change). Logs are in this session's scratchpad,
under `leandb-m2-wave15/`.

| Gate | Result |
| --- | --- |
| `lake build leandb_tests leandb_ddd_tests` | exit 0, 166 jobs; the axiom audit includes the 7 new laws (only `propext`/`Classical.choice`/`Quot.sound`) |
| `.lake/build/bin/leandb_tests` | exit 0, "all engine tests passed": M14b 142, M14c 105, M15a 572 random cases, D1–D10 agree, all migration tests |
| `.lake/build/bin/leandb_ddd_tests` | exit 0: the M1 member-set checks, then the 5 M2 sections (94 assertion call sites, 29 meaning-differential call sites) |
| `python3 scripts/ddd_negative.py` | exit 0: 9 intended rejections (4 M1 + `MissingConflict`, `SwappedLink`, `UnprovenGuests`, `WrongFill`, `UnknownFillField`), plus the imported cascade run |
| `python3 scripts/ddd_bridge.py runs/partiful-m2/frozen/leanreact --spec <spec>` | exit 0 against the frozen copy: 6 populated fixtures (adds `GateEvolution`) and 7 intended rejections, including the authored Partiful `Domain.lean` |
| `git diff --check` (+ trailing-whitespace scan of new untracked files) | exit 0; no trailing whitespace in the new files |

Protected files, SHA-256, equal to `runs/partiful-m2/baselines/LeanDB-worktree.tgz`:
`CHANGELOG.md` 86a47d9a…352c3, `docs/roadmap.md` 2c66dac1…6f, `docs/typed-interface.md`
ed35de28…dd4 (full hashes in the final report).

`TestsDddM2` has 94 assertion call sites in five sections. Each write is
compared with its pure meaning on the full state and counters (29
`compareTxn`/`compareRead` call sites), with WF checked before and after:

1. **Rsvp entity.** Typed conflict, idempotent RSVP, missing-reference abort,
   rollback, both `findBy`s and their plans, the semi-join with its order, plan
   and no hydration, the visibility matrix, `Changes`, restrict, cascade,
   `declareCascade`, and dropped-table denial.
1a. **Foreign-key indexes.** Which columns get one; the restrict and cascade
   `EXPLAIN` plans; an existing database without the index (wave 1.5 above).
2. **Gate refusal and backfill.** The baseline `schemaMismatch`; refusal naming
   `Party.guestList` with state, fingerprint and journal unchanged; `--check`
   exits 3, then 0 once the migration is declared; backfill to `.everyone` with
   every other field kept and the counter preserved (deleted id 3 is not
   reused); the named record and journal entry; the next id is 4; reopening is
   `upToDate`.
3. **Duplicate preflight.** All rows `[1,3]` and `[2,5,6]` with their keys, plus
   the canonical-email collision `[1,4]`, reported together; nothing applied and
   no index; after the data is fixed, the change applies and `.uniquePhone`
   reaches code as a typed conflict.
4. **Atomicity.** With the preflight off, a person column, a party rewrite and
   then a failing unique are all rolled back: state, columns, scratch tables,
   fingerprint, version, journal and record.

**Incident (wave 1.5).** The scratchpad is shared with other workers, and my
`gates.sh` there had been overwritten by the leanapi worker's gate script. One
background run therefore executed *that* script. It ran in
`/Users/harshwork/code/leanapi`:

- It edits no sources and runs no git write command.
- It built into leanapi's ignored `.lake/ddd-common`.
- It rewrote leanapi's `.lake/ddd-m2-*` logs and `.lake/ddd-m2-gates.summary`
  (at about 00:32–00:34), which now show `partiful_build`, `common_build` and
  `check_partiful` at exit 1.

I could not tell whether those failures are their work in progress or
contention. The leanapi worker should re-run its own gates. My LeanDB gates
were then re-run from uniquely named files.

The two mutation checks fail exactly as expected (log in the scratchpad), and
`Migration.lean` was restored and hash-verified.

## Interface changes

- **`Read` gains a constructor, `linkField`.** No peer matches on `Read`
  constructors exhaustively (checked by grep in leanapi and leanreact).
  `denote`/`exec` are extended, and no law needed changes.
- **Migration engine behavior.**
  - A rebuild keeps the AUTOINCREMENT counter.
  - A transform rebuild creates its indexes inside the migration transaction,
    so a violating unique index now fails the migration atomically instead of
    failing at the next open.
- **`fetchFiltered` builds its SQL through the new public `filteredSelectSql`.**
  The bytes are unchanged.
- **Wave 1.5: foreign-key indexes.** `Conn.verify` and migrations create the
  engine `_leandb_fk_*` indexes. `validateSchema` refuses declared index names
  starting `_leandb_`. The importer ignores `_leandb_*` indexes. `countRefsDb`
  takes its SQL from `ReferencedBy.countSql` (the bytes are unchanged).
  Fingerprints are unchanged.
- **Native names versus the post's portable names.**
  - `Unique α` / `Rsvp.Unique.onePerGuest` stand where the post has
    `Rsvp.Conflict.onePerGuest`.
  - `Read`/`Txn` stand where the post has `Query`/`DB`.
  - `SchemaMigration`/`migration%` stand where the post has `migration`.

  The portable names are wave 2 (LeanReact).
- **Naming decisions.**
  - `LeanDb.Migration` (the chain) already existed, so the typed declaration is
    `SchemaMigration`.
  - `migration%` follows the existing `unique%`/`cascade%` naming, so
    `migration` stays an identifier.

## Decisions (made, recorded)

1. **What the gate makes on its own.** The gate applies exactly the changes
   that invent and reinterpret nothing (listed in A), and refuses everything
   else. It never drops data at startup; the explicit
   `leandb migrate apply --allow-destructive` remains for that.
2. **A covered change is applied at startup** (`Gate.ensure`/`openDb`), as the
   post says: "won't apply the new schema *until* there's a migration".
   `Options.preflight := false` exists only to test atomicity; SQLite still
   refuses inside the transaction.
3. **`migrate --check` exits 0 for a covered pending change**, because startup
   would succeed. The printed `status:` line distinguishes `pending` from
   `up to date`.
4. **Migrations are matched by (table, column), not by order or chain
   position.** A declared migration whose field already exists is simply
   unused, so authors can keep old migrations in the list. Use is recorded by
   name in `_leandb_applied_migrations`, and the step list goes in the journal
   as before.
5. **Unique constraints and the preflight.** New unique indexes are covered
   automatically but always preflighted. A canonicalizing unique adds
   `checkCanonical` (the shared parser) to that preflight.
6. **The semi-join uses `IN`, not `JOIN`.** `IN` is exact on any state, and the
   plan is still the covering pair index. `memberField` keeps its `JOIN`.
7. **The RSVP is `LinkRelation` + `Read.linkField`.** It does not reuse
   `MemberRelation`, because a generic link allows other fields and uniques on
   the edge entity, as the post's `Rsvp` may grow.
8. **Foreign-key indexes are derived and auto-applied, not declared.** They
   stay outside the fingerprint, so adding them never counts as an uncovered
   (or any) schema change, and existing databases and frozen chains keep
   opening. See wave 1.5.

## Remaining gaps

- **The startup gate is not yet wired into the app.** LeanAPI's `app% serve` /
  `DbConns.open` (DDD-LAPI-07) must call `Gate.command?` and `Gate.ensure`
  before opening. Until then, the served app keeps today's opaque
  `schema_mismatch` refusal.
- **Composite uniques from portable declarations:** done in wave 2 (see
  "Wave 2"), and `Rsvp.onePerGuest` is a native unique.
- **Stale engine FK indexes are not dropped.** An engine FK index on a column
  that stops being a reference is only dropped when its table is rebuilt.
  Such an index is harmless.
- **Gate coverage is limited.** The gate does not yet cover:
  - renames or retypes (those need a typed transform, via the existing chain
    `Step`)
  - optional→required with a fill
  - concurrent first-open of several processes (startup concurrency is not
    claimed, as in M1)
- **Raw native operations are module-scoped by Lean only for portable
  generated names.** `LeanDb.Txn.insert` etc. stay callable by any module that
  imports LeanDb. Privacy relies on the portable `Op`/`DB` exposing no lift from
  an arbitrary `Txn` (see C.8).
- **Not claimed:** formal SQLite/FFI correspondence (as in M1), and the
  general cascade-WF proof.

## C. What wave 2 needs from the portable layer

To wire B to `constraint` / `Conflict` / `findBy` / `Query` / `DB`, the
LeanReact portable layer must provide the following.

1. **Constraint descriptors visible at `native_schema%` time** (persisted across
   imports). For each `constraint T.name : unique …`, LeanDB needs:
   - the owner `T`
   - the constraint name (the constructor name)
   - the ordered list of *direct* field paths (one or more), as kernel-reducible
     data like today's `Unique.field` / `FieldPath.identity`, so
     `native_schema%` can generate `nativeFieldAgreement` and a composite
     `nativeKeyAgreement : encodeKey ix (keyOf ix r) = #[toCol (p₁.get r), toCol (p₂.get r)]`
     by `rfl`
   - a stable semantic identity string per constraint, for `sourceUnique`

   LeanDB then registers the native `unique%` entry itself.
2. **`T.Conflict` and its native correspondence.** LeanDB needs the name of
   `T.Conflict` and the guarantee that its constructors are exactly the
   constraint names, in declaration order. `native_schema%` will then generate
   `T.conflictOf : Unique T → T.Conflict`, plus its inverse and a round-trip
   proof, by constructor name. This is not a field search.
3. **The failure model of `DB`.** Native `Txn.insertUnique v missingRef` needs:
   - the portable *framework* failure that a missing reference maps to, so that
     foreign-key failures stay out of `Conflict` (the post's `Party.insert :
     DB (Id Party)`)
   - confirmation that a `DB`/`Op` abort rolls back the whole operation
     (native `Txn.throw` does)
4. **`Query` and `DB` primitives with types**, so LeanDB can interpret them as
   `Read s` and `Txn σ s ε`:
   - `find`
   - `findBy` (curried for composites → the native tuple key)
   - `insert`
   - `update`/patch with `Changes`
   - `delete`
   - the guests projection

   LeanDB also needs a way to build `Row T` from a `Valid T`. Today that is
   `LeanApp.Domain.Trusted.row`; keep it or replace it with an equivalent.
5. **Delete actions on references.** For each `onDelete := cascade` reference
   (on `Rsvp.party`), LeanDB needs `(T, field)` before deriving, so
   `native_schema%` can call `Derive.declareCascade`. The default stays
   RESTRICT.
6. **Typed joins.** A portable descriptor of `Rsvp ⋈ Person`: the edge entity
   and its parent and target reference fields, plus the selected target field
   (`name`) as a typed path. LeanDB will generate the `LinkRelation` (laws by
   `rfl`, as the bridge fixture shows for portable `Ref`) and reuse
   `HasFieldProjection` for the column. `Party.guests … (h : CanSeeGuests …)`
   then lowers to `Read.linkField`, and the `if h :` branch lowers to
   `Read.discloseIf`.
7. **`deriving Changes (except := …)`.** LeanDB needs the included field names,
   so it can build `Fields.of [...]` and the merged `Checked` row for
   `Txn.patch`. No other native support is needed.
8. **Privacy.** `deriving Entity (private := …)` must generate the *portable*
   raw operations as Lean `private` names. The portable `Op`/`DB` must not
   expose a public lift from an arbitrary `LeanDb.Txn`; the native interpreter
   must be the only bridge.
9. **Migrations.** The post spells it `migration addGuestList := Party.addField
   guestList (fill := .everyone)`. The portable layer can re-export LeanDB's
   `migration%`, or elaborate its own spelling to
   `LeanDb.SchemaMigration.addField Party Party.DbField.guestList (fill := …)`.
   It must collect a domain's migrations into one `List SchemaMigration` for
   the app's `main` (LeanAPI, DDD-LAPI-07).

## Wave 2: wired to the portable layer

Built against the LeanReact wave 1 snapshot
`runs/partiful-m2/frozen-w2/leanreact`, not the live repo. All wave 2 changes
are in the optional bridge (`adapters/domain`), its fixtures and
`scripts/ddd_bridge.py`. Core `LeanDb` is unchanged since wave 1.5.

### What landed

- **Composite constraints in `native_schema%`.** Every `constraint` /
  `private constraint` is read from the portable registry
  (`LeanApp.Domain.Deriving.constraintDeclarations`). Single-field constraints
  keep the milestone 1 path. A composite one becomes a native unique index in
  declared field order, for example
  `Rsvp.Unique.onePerGuest` → `uq_rsvp_onePerGuest (party, guest)`. Native
  alternatives follow declaration order, as `T.Conflict` does.
  - The identity mapping is exact: `sourceUnique .onePerGuest =
    Rsvp.onePerGuest.key.identity = "Rsvp.onePerGuest"`.
  - The agreement theorem is `Rsvp.onePerGuest.nativeKeyAgreement`:
    `keyOf ix r = key.key r ∧ encodeKey … = #[toCol r.party, toCol r.guest]`,
    by `rfl` and axiom-audited.
- **Typed lookup evidence.** `storageResources s` sets
  `unique := fun storage key => UniqueStorage storage key`. `native_schema%`
  generates `HasUniqueStorage s T K T.c.key` for every declared constraint,
  single and composite. The generic instance gives
  `HasUniqueResource (storageResources s) T K storage key`.
  - It reconciles the request's `HasEntityResource.witness` (which is not
    reducible, so it cannot index an instance) with the schema's dictionary
    through `SameStorage`, a reflexive class that asks the unifier.
  - The instance pinned as missing in LeanReact's `NativePost.lean` now
    resolves: `getParty.Requirements.infer` against the native family.
  - A hand-built key with the same identity and fields gets no evidence
    (rejection fixture `UndeclaredUniqueKey`).
- **Storage-step hooks** (`LeanDbDomain.Operations`). There is one hook per
  request; signatures are below. The details:
  - `insert` goes through `Txn.insertUnique`.
  - A declared conflict is a value: `.error c.publicFailure` for the request's
    constraint whose identity equals `sourceUnique index`.
  - `update` re-reads the row and writes only the changed columns, so only
    constraints touching them are checked.
  - `delete` cascades `cascade%`-declared references and aborts when
    restricted.
  - `findBy` probes the native index with `lookup.encode key`.
  - `select` returns rows by id.
  - Framework failures are a typed `StorageFault`, mapped by the caller and
    aborting the `Txn`.
- **The typed join (item 4).** `native_schema%` generates
  `HasLinkStorage s E parentField targetField P T` for every ordered pair of
  required references, for example `Rsvp "party" "guest" Party Person`, with
  `rfl` column laws.
  - `LinkStorage.project` lowers to `Read.linkField`: names only, by guest id.
  - `LinkStorage.projectIf` lowers to `Read.discloseIf`. The theorem
    `projectIf_denied` states that a denied read is `pure hidden`.
  - LeanReact's portable join request does not exist yet (not in the
    snapshot, not in the live repo). I implemented the hook natively, tested
    it on the post's records, and proposed the portable shape in the
    checkpoint (below).
- **The post's domain runs natively** (`adapters/domain/Tests/PostRuntime.lean`).
  It imports LeanReact's `PostPart1` byte for byte (the bridge copies and
  compiles it) and runs it on SQLite through the shared `Flow.run`. A test-only
  algebra uses nothing but these hooks. Every operation is compared with
  `Txn.denote`/`Read.denote` on the full state, counters included, with WF
  checked:
  - `createPerson` ×4; `emailTaken` for the exact and the canonical
    (`Asha@Example.TEST`) email, with the state unchanged.
  - `Person.findBy` ×4, `hostPartyAs` ×3, `Party.select`, `rsvpAs` ×6.
  - A second yes, and the raw `Rsvp.insert` duplicate (`onePerGuest` as a
    value), with the state unchanged; `rsvpAs` to a missing party gives
    `notFound`.
  - The `getParty` matrix:

    | Visibility | Host | Attendee | Visitor | Signed out |
    | --- | --- | --- | --- | --- |
    | `everyone` | sees | sees | sees | sees |
    | `attendees` | sees | sees | hidden | hidden |
    | `hostOnly` | sees | hidden | hidden | hidden |

  - `Person.update` to a taken email returns `uniqueEmail` and writes
    nothing; to a free email it succeeds.
  - `Person.delete` of a guest is `restricted` (`rsvp.foreignKey.guest`) and
    rolls back.
  - `Party.delete` cascades only that party's two RSVPs, keeping counters,
    and the cancelled party is then `notFound`.
  - The join's names come back by guest id. The portable select loop answers
    `[Dev, Ben]` (RSVP order); the join answers `[Ben, Dev]`.
  - `EXPLAIN` shows `COVERING INDEX uq_rsvp_onePerGuest (party=?)` for the
    join and `uq_rsvp_onePerGuest (party=? AND guest=?)` for `Rsvp.findBy`.
  - With the RSVP table dropped, the denied join still answers `hidden` and
    the allowed one fails.
- **Milestone 1 fixture kept working.** `PartifulProjection`'s test algebra
  gains the two new query requests (`findBy`, `select`), which its domain
  never builds, so it compiles against the new `RequestF`.

### Interface for peers (wave 2, exact)

```lean
-- [LeanDbDomain.Witness]
structure UniqueStorage {s T K} [IsSchema s] (storage : EntityStorage s T) (key : LeanApp.Domain.UniqueKey T K) : Type 1 where
  index : @LeanDb.Unique T storage.entity storage.unique
  encode : K → @LeanDb.Unique.Key T storage.entity storage.unique index
  identity_agrees : storage.sourceUnique index = key.identity
  key_agrees : ∀ record : T, encode (key.key record) = @LeanDb.Unique.keyOf T storage.entity storage.unique index record
class HasUniqueStorage (s T K) [IsSchema s] [HasEntityStorage s T] (key : UniqueKey T K) : Type 1 where
  lookup : UniqueStorage (HasEntityStorage.storage (s := s) (T := T)) key
class SameStorage {s T} [IsSchema s] (a b : EntityStorage s T) : Prop where same : a = b   -- only instance: a a
structure LinkStorage (s Parent Target Edge) [IsSchema s] : Type 1 where
  parent : EntityStorage s Parent;  target : EntityStorage s Target;  edge : EntityStorage s Edge
  relation : @LinkRelation Parent Target Edge parent.entity target.entity edge.entity
class HasLinkStorage (s Edge) (parentField targetField : String) (Parent Target : outParam Type) [IsSchema s] : Type 1 where
  storage : LinkStorage s Parent Target Edge
-- [LeanDbDomain.Resources]
storageResources s := { … , unique := fun storage key => UniqueStorage storage key }
instance [HasEntityStorage s T] (storage : (storageResources s).entity T) (key : UniqueKey T K)
  [HasUniqueStorage s T K key] [SameStorage (HasEntityStorage.storage (s := s) (T := T)) storage] :
  HasUniqueResource (storageResources s) T K storage key
-- [LeanDbDomain.Operations]   all: {s T …} [IsSchema s] [LeanApp.Domain.Entity T]; ε, σ, Scope generic
inductive StorageFault | invalidReference (why : String) | invalidIdentity (why : String) | invalidRow (checks : List String)
  | missingReference (constraint : ConstraintMetadata) | restricted (constraint : ConstraintMetadata)
  | unmappedConflict (constraint : ConstraintMetadata) | gone
def StorageFault.code : StorageFault → String
def EntityStorage.insert (storage : EntityStorage s T) (value : T) (conflicts : List (Constraint C))
    (fault : StorageFault → ε) : Txn σ s ε (Except C (Ref T))
def EntityStorage.update (storage) (row : Row Scope T) (patch : Change T) (conflicts : List (Constraint C))
    (fault : StorageFault → ε) : Txn σ s ε (Except C Unit)
def EntityStorage.delete (storage) (row : Row Scope T) (fault : StorageFault → ε) : Txn σ s ε Unit
def EntityStorage.find (storage) (reference : Ref T) : Except String (Read s (Option (Row Scope T)))   -- milestone 1
def EntityStorage.findBy (storage) {key : UniqueKey T K} (lookup : UniqueStorage storage key) (value : K) :
    Read s (Except StorageFault (Option (Row Scope T)))
def EntityStorage.select (storage) : Read s (Except StorageFault (List (Row Scope T)))
def EntityStorage.rowOf (storage) (row : Valid T) : Except StorageFault (Row Scope T)
def LinkStorage.project [LeanApp.Domain.Entity P] (link : LinkStorage s P T E) (column : @FieldStorage T V link.target.entity)
    (parent : Ref P) : Except String (Read s (List V))
def LinkStorage.projectIf … (parent : Ref P) (allowed : Prop) [Decidable allowed] (visible : List V → β) (hidden : β) :
    Except String (Read s β)
theorem LinkStorage.projectIf_denied … (denied : ¬ allowed) (lowered : link.projectIf … = .ok read) : read = .pure hidden
```

Lowering, as `PostRuntime` and LeanAPI do it:

| Request | Hook |
| --- | --- |
| `RequestF.insert storage value conflicts` | `storage.insert value conflicts fault` |
| `.update storage row patch conflicts` | `storage.update row patch conflicts fault` |
| `.delete storage row` | `storage.delete row fault` |
| `.findBy storage _ lookup key` | `storage.findBy lookup key` |
| `.select storage` | `storage.select` |
| `.find` | as in milestone 1 |

Each case does `letI := inst` with the constructor's `[Entity T]`. A family
that composes `storageResources` (LeanAPI's `{ storageResources s with auth :=
… }`) must forward `HasUniqueResource`, as it already forwards the projection
instance.

**Proposed portable join shape** (sent to `main` for LeanReact):

- `structure LinkKey (E P T) := identity : String; parent : E → Ref P;
  target : E → Ref T`
- a slot `ResourceFamily.link : entity E → LinkKey E P T → Type 1`, which
  LeanDB instantiates with `LinkStorage`
- `RequestF.linkField (storage : entity E) (key : LinkKey E P T)
  (link : resources.link storage key) (column evidence for FieldPath T V)
  (parent : Ref P) : RequestF … k (List V)`

The authored `if h : CanSeeGuests … then … else .hidden` needs no IR node,
because the request exists only in the `then` branch.

### Commands run (wave 2, final sources)

All runs use `LEAN_NUM_THREADS=2`. The script is
`.lake/ddd-m2-scratch/leandb-gates-w2.sh` (repo-private, as the scratch rule
requires), with logs in `.lake/ddd-m2-scratch/leandb-w2-*.log`.

| Gate | Result |
| --- | --- |
| `lake build leandb_tests leandb_ddd_tests` | exit 0, 166 jobs |
| `.lake/build/bin/leandb_tests` | exit 0, all engine tests, 572 M15a cases |
| `.lake/build/bin/leandb_ddd_tests` | exit 0, 6 sections (M1 + 5 M2) |
| `python3 scripts/ddd_negative.py` | exit 0, 9 intended rejections |
| `python3 scripts/ddd_bridge.py runs/partiful-m2/frozen-w2/leanreact --spec <spec>` | exit 0: 7 populated fixtures (adds `PostRuntime`) and 8 intended rejections (adds `UndeclaredUniqueKey`), plus the M1 Partiful domain |
| `git diff --check` | exit 0; no trailing whitespace in the new files |

The bridge recompiled the frozen-w2 portable layer into the existing
`.lake/ddd-portable`; no second build tree was created. The protected files are
still byte-identical to the baseline.

### Remaining gaps (wave 2)

- **No portable `onDelete := cascade` yet.** The assembly module declares
  `cascade% Rsvp.party` before `native_schema%`.
  `LeanDb.Derive.declareCascade` is ready for `native_schema%` to call once
  LeanReact records the reference action.
- **The portable join request is not defined yet.** `Party.guests` in
  `PostPart1` is still the `Rsvp.select` loop, which returns RSVP order and
  reads every RSVP. Wiring needs LeanReact's `RequestF` node and resource
  slot.
- **LeanAPI's production algebra must still add the five request cases,**
  using these hooks, and forward `HasUniqueResource` for its composed family.
- **Private raw operations (decision 13) stay portable.** Decision 13's
  `Rsvp.findBy` privacy is the portable layer's; natively,
  `LeanDb.Read.findBy` remains callable by any module that imports LeanDb (the
  trust boundary is unchanged from wave 1).
- **Disk was about 1.0 GB free after the last gate run.**

## Wave 2.5: LeanReact cp2 compatibility, `Credential`, generality

The bridge now builds against `runs/partiful-m2/frozen-w2/leanreact-cp2`, a
superset of cp1. It recompiled into the existing `.lake/ddd-portable`; no second
build tree was created.

### What changed

- **The portable join is wired.** `storageResources s` sets
  `link := LinkEvidence` and `column := ColumnEvidence`. `native_schema%`
  generates:
  - `HasLinkEvidence s E P T E.link.<a>.<b>` for each generated `LinkKey`, with
    `parent_agrees`/`target_agrees` by `rfl`
  - `HasColumnEvidence s T V T.<field>Path` for each direct column whose type has
    a `Wire` codec

  Generic `HasLinkResource`/`HasColumnResource` instances use the same
  `SameStorage` check as `HasUniqueResource`. `RequestF.linkField` lowers through
  `LinkEvidence.project targets column parent` to `Read.linkField`. Every
  requirement now resolves natively, including `getParty`'s link and column
  requirements.
- **Core: `LinkRelation` takes only the edge's dictionary**
  (`structure LinkRelation (parent target edge) [Entity edge]`). Its fields never
  used the parent or target dictionaries, so a link applies to the request's own
  target storage without restating it.
- **`PasswordHash` columns.** The bridge adds a `ColCodec PasswordHash` (TEXT,
  through `Trusted.passwordHashText`/`passwordHash`) and a
  `LawfulColCodec PasswordHash` proved by `rfl`. A field whose type has no `Wire`
  gets no `HasFieldStorage`, `HasFieldProjection` or `HasColumnEvidence`. So the
  hash is a column, but no portable read can select it.
  `LibraryRuntime` checks by `run_cmd` that `Wire PasswordHash`, the column
  evidence and `HasColumnResource` for the hash do not resolve.
- **Test algebras** (`PostRuntime`, `LibraryRuntime`, `PartifulProjection`)
  lower `linkField`. They refuse `hashPassword`, `verifyCredential` and
  `startSession` explicitly, because those are LeanAPI's KDF steps.
- **Library code is general.** No library docstring names Partiful concepts
  or "the post". The examples are `Order`/`Customer` and `Book`/`Loan`/`Member`
  (Gate, Link, Schema, Read, Entity, and the bridge's Witness, Schema, Operations,
  Storage and Access). `LinkStorage`/`HasLinkStorage` are generated for every
  ordered pair of required references, a uniform rule rather than a shape guess.

### Fixtures

- **`PostRuntime` (cp2 `PostPart1`, byte-identical)** additionally covers:
  - `getParty` through the native join, with guests by guest id (`[Ben, Dev]`)
    across the visibility matrix
  - `Rsvp.add` returning the conflict value
  - `edit` with `Party.Changes`, which writes the title and keeps host and date
  - a cascade through `EntityStorage.delete`, since `Party.delete` is
    `internal`
  - a `Credential` row whose hash reads back exactly
- **`LibraryRuntime` (new generality fixture).** It uses `Member`/`Book`/`Loan`/
  `MemberCredential` and public API only:
  - `constraint Loan.onePerMember : unique (book, member)`, `internal`,
    `deriving Changes`
  - `cascade% Loan.book`, and `migration% addShelf := Book.addField shelf
    (fill := .general)` on a database made before the field existed: the gate
    refuses, then backfills
  - an email conflict and a duplicate loan, both with nothing written
  - `Member.findBy`, and the composite `Loan.findBy`
  - both joins: `borrowers` gives `[Ada, Cy]` by member id although Cy borrowed
    first, and `loanHistory` gives titles by book id
  - `EXPLAIN` plans: `COVERING INDEX uq_loan_onePerMember (book=?)` and
    `INDEX _leandb_fk_loan_member (member=?)`, with no scan
  - `Member.patch` with Changes
  - a restricted member delete (`loan.foreignKey.member`, rolled back)
  - a book delete that cascades its loans
  - a TEXT hash column that round-trips

  Every step is compared with the meaning on the full state and counters.

### Commands (cp2, final sources)

The script is `.lake/ddd-m2-scratch/leandb-gates-cp2.sh`, with logs in
`.lake/ddd-m2-scratch/leandb-cp2-*.log`.

| Gate | Result |
| --- | --- |
| `lake build leandb_tests leandb_ddd_tests` | exit 0, 166 jobs |
| `.lake/build/bin/leandb_tests` | exit 0, 572 M15a cases, all engine tests |
| `.lake/build/bin/leandb_ddd_tests` | exit 0, 6 sections |
| `python3 scripts/ddd_negative.py` | exit 0, 9 intended rejections |
| `python3 scripts/ddd_bridge.py runs/partiful-m2/frozen-w2/leanreact-cp2 --spec <spec>` | exit 0: 8 populated fixtures (`Access`, `UniqueSources`, `Storage`, `ProjectionEvolution`, `GateEvolution`, `LibraryRuntime`, `PostRuntime`, `PartifulProjection`), 8 intended rejections |
| `git diff --check` | exit 0, plus a trailing-whitespace scan of the new files |

The protected files are byte-identical to the baseline.

### Interface additions for peers (exact)

```lean
structure LeanDb.Domain.LinkEvidence {s E P T} [IsSchema s] (edges : EntityStorage s E) (key : LinkKey E P T) : Type 1 where
  parentIdentity : Ontology.HasTypeId P;  targetIdentity : Ontology.HasTypeId T;  link : LinkStorage s P T E
  parent_agrees : ∀ edge, link.relation.getParent edge = ⟨Int64.ofInt ((key.parent edge).key.toInt?.getD 0)⟩
  target_agrees : ∀ edge, link.relation.getTarget edge = ⟨Int64.ofInt ((key.target edge).key.toInt?.getD 0)⟩
structure LeanDb.Domain.ColumnEvidence {s T V} [IsSchema s] (storage : EntityStorage s T) (path : FieldPath T V) : Type 1 where
  column : @FieldStorage T V storage.entity;  source_agrees : column.source = path
def LeanDb.Domain.LinkEvidence.project (evidence : LinkEvidence edges key) (targets : EntityStorage s T)
    (column : ColumnEvidence targets path) (parent : Ref P) : Except String (Read s (List V))
-- lowering: | @RequestF.linkField _ _ _ _ _ _ _ _ _ _ _ _ link targets _ column parent => link.project targets column parent
instance : ColCodec PasswordHash;  instance : LawfulColCodec PasswordHash
structure LeanDb.LinkRelation (parent target edge : Type) [Entity edge]   -- was [Entity parent] [Entity target] [Entity edge]
```

### Remaining (wave 2.5)

- **The credential hash is read through `EntityStorage.select`.**
  `verifyCredential`'s lowering is LeanAPI's. Reading a credential row by person
  can use `select` now; an indexed hook can be added if needed.
- **The cascade is still `cascade% Loan.book` / `Rsvp.party`** in the assembly
  module, because it isn't portable yet.

## Wave 3: LeanReact cp3 compatibility

The bridge builds against `runs/partiful-m2/frozen-w2/leanreact-cp3`. Wave 3 has
no core `LeanDb` changes.

- **Portable cascade.** Before deriving a native entity, `native_schema%` reads
  `LeanApp.Domain.Deriving.cascadeDeclarations`
  (`constraint Loan.removeWithBook : cascade book`). It records each entry with
  `LeanDb.Derive.declareCascade`, which is idempotent. `cascade%` keeps working,
  and `TestsDddM2` and `GateEvolution` still use it. The fixtures no longer use
  `cascade%`: the post's `constraint Rsvp.cancelWithParty : cascade party` and
  the library's `Loan.removeWithBook` alone make delete cascade. Both runtime
  fixtures would fail with `restricted` otherwise.
- **Explicit links.** `HasLinkStorage` and `HasLinkEvidence` are generated only
  for a declared `link E.parent E.target`, detected by its `E.link.<parent>.<target>`
  constant. Nothing is inferred from an entity's shape. `PostRuntime` checks that
  the declared `Rsvp.party → Rsvp.guest` has evidence and the undeclared reverse
  has none.
- **Explicit credentials.** `PostPart1` declares
  `credential Credential.person Credential.hash`, and `LibraryRuntime` declares
  `credential MemberCredential.member MemberCredential.hash`. The `PasswordHash`
  column codec is type-based and unchanged; both fixtures store a hash and read
  it back. LeanDB does not use `CredentialLink`, so the `person` → `profile`
  rename does not affect it.
- **Wire codecs.** Payload-free errors now render as bare strings (e.g.
  `"emailTaken"`), and the fixture expectations were updated. The native storage
  codecs (closed enums, `Ref`, `Instant`, scalars) are unaffected, as the
  populated runs confirm: migration backfill, enum columns and refs all round-trip.
- **Library docs** describe links as declared, and cascades as portable or
  `cascade%`. Library code still names no Partiful concept.

- **Milestone 1 `PartifulProjection`** now expects the hidden disclosure as
  the bare string `"hidden"`, which still carries no payload or count.

The gates are run by `.lake/ddd-m2-scratch/leandb-gates-cp3.sh`, with logs in
`.lake/ddd-m2-scratch/leandb-cp3-*.log`.

| Gate (cp3, final sources) | Result |
| --- | --- |
| `lake build leandb_tests leandb_ddd_tests` | exit 0, 166 jobs |
| `.lake/build/bin/leandb_tests` | exit 0, all engine tests |
| `.lake/build/bin/leandb_ddd_tests` | exit 0, 6 sections |
| `python3 scripts/ddd_negative.py` | exit 0, 9 intended rejections |
| `python3 scripts/ddd_bridge.py runs/partiful-m2/frozen-w2/leanreact-cp3 --spec <spec>` | exit 0: 8 populated fixtures including `PostRuntime` and `LibraryRuntime`, 8 intended rejections |
| `git diff --check` | exit 0; no trailing whitespace in the new files |

The protected files are byte-identical to the baseline.

## Structured values in one column

**Investigation** (against `frozen-w2/leanreact-cp4`, before the change): the
portable layer accepts `structure Basket where items : List Item; deriving Entity`
(`Item` a record of two payload-free enums) and a record field `extra : Item`.
`native_schema%` refused both:

- The list was refused with: `field 'items' of Basket is 'List Item' but Item is
  not an Inline record; a child table needs 'deriving LeanDb.Inline' … (or give
  'List Item' a ColCodec of its own to store it as one column)`.
- The record was refused with: `failed to synthesize LeanDb.ColCodec Item`.

**Rule.** In `native_schema%`, a field type with a portable `StorageCodec`, no
native `ColCodec`, and that is not a payload-free enum (those stay closed-world
TEXT with a CHECK, as before) gets `storageColCodec` (in
`LeanDbDomain.Storage`). This covers a list, a record, a variant with payloads,
and a represented type. The rule is type-directed and covers no app names.

- **Storage** is one TEXT column holding the canonical JSON of the codec's
  `encode` (`Lean.Json.compress`, keys in order).
- **Reads** parse the text and decode it through the same codec, checks
  included, on every read. Text that isn't JSON, or a value the codec refuses,
  is a typed `DbError.decode table column`. A read reports it as
  `DbFault.corruption "<table>.<column>: …"`; it is never a substitute value.
- **Fingerprint.** The column's shape is `wire:<schema JSON>`, so it is in the
  fingerprint. The engine refuses a migration across a changed stored schema by
  name (`externalShapePrefix`, in core `Migrate.lean`), because old values may
  not decode.
- **Decision: no SQL CHECK** (no `json_valid`). The codec's decode, including
  checked constructors, is the authoritative check and runs on every read. A
  `json_valid` CHECK would catch only a subset, change the DDL of every such
  column, and stand in the way of raw-SQL repair.
- **Migrations.** Adding such a field needs a fill, as for any required field:
  `migration% addDelivery := Order.addField deliverTo (fill := Address.mk .pickup 0)`.
  The fill is stored through the same codec.
- **Payload-carrying inductives** are no longer sent to `deriveClosedEnum`
  (which refused them). They take the JSON column when they have a
  `StorageCodec`.

**Test: `adapters/domain/Tests/JsonColumnRuntime.lean`.** This is a kitchen
domain from public API only, run on SQLite. Each step is compared with
`Txn.denote`/`Read.denote` on the full state and counters, with WF checked:

- `Order.lines : List Line`, a list of records of two enums.
- `Order.deliverTo : Address`, a record with an enum and a `Nat`.
- An old database without `deliverTo`: the gate refuses, then backfills, and
  the old lines are kept.
- A changed `Line` schema (a new field) is refused by name.
- The stored text equals the canonical wire JSON.
- `placeOrder` and `orderLines` through `Flow.run`.
- `Order.update` round-trips the whole list.
- Corruption written with raw SQL is a `corruption` fault naming the column:
  - `not json`
  - an unknown constructor
  - a missing record field
  - an unknown key in a record

**Represented private-constructor types: `adapters/domain/Tests/RepresentRuntime.lean`.**
This test builds against the committed live LeanReact (`1a25ecf`, read-only)
and uses `represent Slot as Nat × Nat by Slot.toPair checked Slot.check`.
`Slot` has a private constructor and needs `start < finish`, and is a field of a
`Booking` alongside `seats : List Seat` (a list of records). No LeanDB change
was needed: `represent` gives `Slot` a `StorageCodec`, and the rule above
applies unchanged. The test checks:

- the stored text is the representation's canonical JSON (`[9,11]`)
- reads go through `Slot.check`
- `moveTo` (`Booking.update`) round-trips
- a stored `[16,14]`, which fails the check, and a stored `"noon"`, which has
  the wrong shape, are both `booking.slot:` corruption faults
- a seat with an unknown aisle is a `booking.seats:` fault

No `Slot` is built other than through its codec.

`scripts/ddd_compile_portable.py` now reads imports only from a module header,
as Lean does. An `import` inside a doc comment, such as in `LeanApp/Core.lean`,
had made a module "import itself". The script also guards against cycles.

## M3: LeanDb.Model

LeanDB now owns the data model. It no longer depends on LeanReact: the old bridge
(`adapters/domain`, `scripts/ddd_bridge.py`, `scripts/ddd_compile_portable.py`)
is gone. LeanReact was only read during this phase, never edited.

### Layout

- `lakefile.toml` requires `leanontology` from git at revision
  `322a4c12631dd8ece6ae9841a5e6b630d08d1e3b`; the manifest pins the same revision.
- Three separate libraries hold `LeanDb` (the engine, unchanged API),
  `LeanDbModel` (`LeanDb.Model`, portable), and `LeanDbNative`
  (`LeanDb.Native`, the model on SQLite). The default build includes all three.
  Keeping their roots separate also lets precompiled client consumers load
  the engine without implicitly loading model code.
- `scripts/ModelClosure.lean` checks that the import closure of `LeanDb.Model` is
  only `LeanDb.Model.*`, `LeanOntology.*`, `Lean`, `Std` and `Init`. Today that is
  1449 modules.

**Decision: fold the bridge into LeanDB proper as `LeanDb.Native.*`.** The bridge
used to compile out of tree against a peer checkout. Now it is ordinary LeanDB
code, built and tested by Lake with everything else. Keeping it separate had no
remaining benefit, because both its imports (the core and the model) live in this
repo.

### Modules

`open LeanDb.Model` exports:

| Module | What it provides |
| --- | --- |
| `LeanDb.Model.Metadata` | `Domain`, `Entity`, `FieldType`, `FieldKind`/`FieldMetadata`/`EditorMetadata`, `StorageCodec`, `HasRecord`, `EditableField`, `NamedField`, `Change` (`set`/`andThen`/`replace`), `UniqueKey`, `Unique`, `LinkKey`, `Constraint`, `Time`, `recordCodec`/`enumCodec`/`variantCodec`. It also re-exports from `Ontology`: `Ref`, `Name`, `Title`, `Text`, `Email`, `Password`, `PasswordHash`, `Session`, `Instant`, with their parsers (`Name.parse`, …). |
| `LeanDb.Model.Represent` | `Representation`, `RepresentationCheck`, and `represent T as R by enc checked dec`. |
| `LeanDb.Model.Resources` | `StorageResources` (fields `entity`, `unique`, `link`, `column`), `Has{Entity,Unique,Link,Column}Resource`, `portableStorage`, and the named instances `portableEntity`/`Unique`/`Link`/`Column`. |
| `LeanDb.Model.Request` | `Access` (`query`/`command`), `OpScope`, `Row Scope T` with `Trusted.row`, `StorageRequest`, `Program`, `Interpreter`, `Program.run`, `Program.toCommand`, `Interpreter.toQuery`, `MonadStorage`, `Program.lift`. |
| `LeanDb.Model.DB` | `DB`, `Query`, `MonadLift Query DB`, and lifts into any `MonadStorage` monad. Also `HasRow`, `Changes`, the generic steps `DB.insert/insertTotal/update/updateTotal/patch/patchTotal/delete` and `Query.find/findBy/select/linkField`, and the scoped `Row T` syntax. |
| `LeanDb.Model.Deriving` | `deriving Domain`/`Entity`, payload variants, `ensureWire`, the env extensions, and the generation helpers. |
| `LeanDb.Model.Entities` | `constraint T.c : unique f` / `unique (f, g)` / `: cascade f`, `private constraint`, `internal T.op, …`, `link E.a E.b`, `entity_operations`, `deriving Changes` and `deriving instance Changes (except := […]) for T`, and the `#print T.Conflict` override. |
| `LeanDb.Model.Requirements` | `derive_requirements f, …` and the generalization machinery (see below). |
| `LeanDb.Model.Memory` | The in-memory backend. |

`LeanDb.Native` exports:

- `storageResources S`, and the evidence types: `EntityStorage`, `UniqueStorage`,
  `LinkStorage`, `LinkEvidence`, `FieldStorage`, `ColumnEvidence`, `SameStorage`.
- The column codecs: the scalars, `Ref`, `PasswordHash`, and `storageColCodec` for
  structured values.
- `native_schema%`, `StorageFault`, and the hooks (`EntityStorage.find/select/findBy/insert/update/delete`,
  `LinkStorage.project/projectIf`, `LinkEvidence.project`).
- The interpreters (`commandRequest`/`commandInterpreter`, `queryRequest`/`queryInterpreter`),
  `Program.toTxn`/`toRead`, and `runCommand`/`runQuery`.

### Storage IR

`StorageRequest (resources : StorageResources) (Scope : Type) : Access → Type → Type 1` has
these constructors:

- `find` (`Option (Row Scope T)`), any access.
- `findBy storage (unique : UniqueKey T K) (lookup : resources.unique storage unique) key`, any access.
- `select`, any access.
- `linkField edges key link targets field column parent` (`List V`), any access.
- `insert storage value (conflicts : List (Constraint C))` (`Except C (Ref T)`), `.command` only.
- `update storage row (patch : Change T) conflicts` (`Except C Unit`), `.command` only.
- `delete storage row` (`Unit`), `.command` only.

How it is used:

- `T.update` and `T.patch` both lower to `update`: `T.update` with `Change.replace`,
  `T.patch` with a lens patch. Conflicts are values. Every other failure belongs to
  the backend.
- `Program resources access Scope` is the free monad over these requests
  (`pure`/`bind`/`request`).
- `DB α := Program portableStorage .command OpScope α`, and `Query α` is the same at
  `.query`.
- A write inside a `Query` is a type error (see the `QueryWrite` fixture).

Extension points for LeanAPI:

- **Embedding.** LeanAPI's operation request type gets one constructor carrying a
  `StorageRequest resources.toStorageResources Scope (accessOf kind) A`. Then
  `instance : MonadStorage portableStorage .command OpScope (Op ε)` makes `DB`
  lift into `Op` (and likewise `Query` into `ReadOp`). The lift is `Program.lift`,
  which is generic, so publication leaves it unfolded.
- **Family.** `structure Resources extends LeanDb.Model.StorageResources where auth : …`.
- **Commands.** `credential C.p C.h` is one more
  `@[command_elab LeanDb.Model.Entities.entityFieldPair]` elaborator. The model's
  elaborator claims only `link` and throws `throwUnsupportedSyntax` for any other
  keyword.
- **Not defined in LeanDB.** `Op`/`ReadOp`, `require`, `Clock`/`Now`, `Principal`,
  `Domain`/`Wire` instances for `Empty`, and `RouteInput`.

### Interpreter interface

- `structure Interpreter (m) resources access Scope where request : StorageRequest … A → m A`.
- `Program.run interpreter program` is the single semantics.
- Backends:
  - In memory: `Memory.interpreter` (any family, `Memory.Engine = StateT Store (Except Fault)`)
    and `Memory.run`. It now enforces references as SQLite does: `missingReference`
    and `restricted` faults, and `Fault.code` uses the same codes as `StorageFault.code`.
  - SQLite: `LeanDb.Native.commandInterpreter fault : Interpreter (Txn σ S ε) (storageResources S) .command σ`
    and `queryInterpreter : Interpreter (ExceptT StorageFault (Read S)) … .query Scope`.
- `Memory.Store` no longer has `now`, `sessions` or `kdfRuns`. Those are operation
  state: LeanAPI wraps the store.

### Requirements and inference

`derive_requirements f` generates, for a `DB`/`Query` definition `f`:

- `f.Requirements : StorageResources → Type 1`
- `f.Requirements.infer : [capabilities…] → f.Requirements r`
- `f.portableRequirements`
- `f.withResources : {r} → f.Requirements r → {Scope} → args → Program r access Scope α`

The machinery is parameterized by `Requirements.Targets`, with these fields:

- `familyType`
- `portable` (the family constant)
- `derived` (`portableStorage ↦ r.toStorageResources` for an extended family)
- `instances` (`Requirements.portableInstances` plus LeanAPI's own)
- `scope`
- `root`

It exposes `inline`, `collectInstances`, `abstractTargets`, `dependencyOrder`,
`withCapabilityBinders`, `generalize targets f body` (LeanAPI passes
`f.flowWithResources` as `body`), `addDefinition`, and `storageNode?`/`storageNodes`. The last two read the kind,
access, entity and constraint identities of each `StorageRequest` in an unfolded
body. That replaces the `RequestF` scan in `#domain_inspect`.

### Dropped (milestone 1)

- **Portable surface:** `Members`, the `member`/`projection`/`auth` family slots,
  `credential` (it moves to LeanAPI), `Principal`, the `<entity>Url` alias,
  `@[entity]`, portable `unique%`, and `Flow`/`Policy`/`Projection`/`SignedIn`/`Viewer`.
- **Bridge:** `MemberStorage`, `HasMemberStorage`, `HasFieldProjection`,
  `ProjectionStorage`, `FieldStorage.project`, and `MemberStorage.contains/project/includeActor`.
- **Bridge fixtures:** `Access`, `Storage`, `ProjectionEvolution`,
  `PartifulProjection`, `MissingProjection`, and `WrongProjection{Target,Getter,Lens}`.
- **Kept:** native `members%` and `unique%` are unchanged.

### Fixes made on the way

- **Unique instance names.** Generated `T.Field`/`T.Conflict` instances, and the
  native `T.Field` `DecidableEq`/`Repr` (`Derive.declareSymbols`), are now named in
  the entity's own namespace. A `deriving` clause had named them `instReprField`
  in the current namespace, so two modules that declared entities at the same level
  could not be imported together.
- **Name resolution.** `native_schema%` now resolves type names the usual way, so
  `open` applies.
- **Exports.** An exported type does not export its namespace, so
  `export Ontology (Name)` alone breaks `Name.parse`. Each function is therefore
  exported explicitly.

### Tests

These are in `TestsModel/`; `leandb_model_tests` runs them.

**Ported from LeanReact (model parts):**

- `Represent` (`Interval`/`SortedList`)
- `Loans`
- `Post` (the post's entities, rules, `Changes`, the requirement inference
  `#guard_msgs`, and `storageNodes` checks)
- `Commands` (new): every declaration command on its own line, a represented
  type with a lambda encoder (`represent Board as List Move by (·.moves) checked
  Board.replay`). The identifier-led commands are wrapped in
  `withPosition(… colGt …)`, so `internal Game.insert` no longer takes the next
  line's `link` as its third identifier. Before the fix it did, and the LeanReact
  syntax still does.

**Run on both backends (`Twin`):**

- `LoansRun`, `PostRun` and `RepresentRun`. Each step runs in memory (the
  portable `f args`) and on SQLite (`f.withResources f.Requirements.infer args`).
- After every step:
  - the answers or fault codes must be equal;
  - SQLite must equal its pure meaning;
  - every table (ids, row JSON, identity counter) must be equal across the two
    backends.

**Ported from the old bridge (SQLite only):**

- `LibraryRuntime` (migration, EXPLAIN plans, `PasswordHash` column)
- `JsonColumns`
- `RepresentNative`
- `GateEvolution`
- `UniqueSources`

**Negative fixtures (`fixtures/model/`, 16):**

- Model: `MissingConflictCase`, `ConstraintAfterUse`, `PrivateFindBy`,
  `InternalSelect`, `ChangesExcludesField`, `RepresentMissing`, and
  `Unsupported{Dependent,Inherited,Payload}`.
- Programs: `QueryWrite`, `ScopeEscape`, `WrongFindId`.
- Native evidence: `UniqueEvolution`, `WrongFieldStorage`, `WrongUniqueGetter`,
  `UndeclaredUniqueKey`.

| Command | Result |
| --- | --- |
| `lake build LeanDb leandb_tests leandb_ddd_tests leandb_model_tests` | exit 0 |
| `.lake/build/bin/leandb_tests` | exit 0 |
| `.lake/build/bin/leandb_ddd_tests` | exit 0 |
| `python3 scripts/ddd_negative.py` | exit 0 (9 rejections) |
| `python3 scripts/ddd_model.py` (replaces `ddd_bridge.py`) | exit 0: closure portable, 8 scenarios, 16 rejections |
| `git diff --check` | clean |

## Next step

1. LeanAPI (phase 3) embeds `StorageRequest` in its operation IR, as described
   in "M3: LeanDb.Model". It uses `Requirements.generalize` with its own `Targets`
   and runs `LeanDb.Native.commandInterpreter` natively.
2. LeanReact (phase 4) imports `LeanDb.Model` in place of `LeanApp.Domain`'s model
   half.
