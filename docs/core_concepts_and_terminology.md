# Core concepts

LeanDB is a typed SQL frontend in Lean 4. Lean describes the data and queries.
SQLite stores the rows and executes the SQL.

Start with the [README](../README.md) for setup. Use the
[glossary](terminology.md) for short definitions and the
[roadmap](roadmap.md) for current limits and future work.

![LeanDB architecture](images/leandb-architecture.svg)

## Types and entities

A domain type describes a value in your application. An entity is a type
that LeanDB can store as a table row.

`deriving LeanDb.Entity` creates the table schema and row codecs.
It also creates typed field symbols for query planning.
Defaults and foreign keys come from the entity declaration.

Here is a small base for notes. Read the Lean blocks on this page in order.

```lean
import LeanDb

open LeanDb

structure Title where
  raw : String
  deriving Repr, DecidableEq, Ord

def Title.make (s : String) : Except String Title :=
  let title := s.trimAscii.toString
  if title.isEmpty then .error "title must be nonempty" else .ok ⟨title⟩

instance : ColCodec Title := ColCodec.via (·.raw) Title.make

inductive Status where
  | draft | published
  deriving Repr, DecidableEq, Ord, LeanDb.ClosedEnum

structure Note where
  title : Title
  body : String
  status : Status := .draft
  deriving Repr, LeanDb.Entity
```

`Title` uses a codec to reject empty titles when decoding database rows or
JSON. `Status` is a closed enum. SQLite stores its names as text and checks
that they belong to the declared set.

A codec defines how a Lean value becomes a SQL column and how it is read
back. Decoding returns either a value or an error. Custom codecs are
responsible for their validation and encoding rules.

### Derive the data, store the validation with it

A closed enum or a plain record — a type that *is* its data — derives its
codec: `LeanDb.ClosedEnum` for enums, `LeanDb.DbJson` for nested JSON
values. Both work in the declaration and, when the portable package must
stay LeanDB-free, post-hoc in the native package with
`deriving instance LeanDb.DbJson for Doc`.

A validated type cannot derive: its Lean type carries proofs that depend
on its data, and a derive has nothing to walk. Store the data
representation and re-decide the proof when reading:

- a validated scalar uses `ColCodec.via`;
- a validated nested type uses `DbJson.via`. It stores and reads the
  data representation and registers that representation's `JsonShape`,
  so the parent derive, the schema fingerprint, and `migrate` all see the
  data shape — and a stored value that no longer passes `parse` fails as
  a typed `DbError.decode` naming the table and field.

```lean
-- Portable package: the proof stays, LeanDB is not imported.
structure Text where
  s : String
  nonempty : 0 < s.length

def Text.make (s : String) : Except String Text :=
  if h : 0 < s.length then .ok ⟨s, h⟩ else .error "text: empty"

-- Native package: store `s`, re-decide `nonempty` on every read.
instance : DbJson Text := DbJson.via (·.s) Text.make
deriving instance LeanDb.DbJson for Run, Paragraph, Doc
```


## Rows and references

`Note` is the value you insert. `Stored Note` is a saved note with its ID.
Use `row.val` for the value and `row.id` for its ID.

`Id Note` is an ID for a note. `Ref Note` is the same type, used for foreign
key fields. An ID for one entity is not an ID for another entity.
SQLite checks whether the referenced row exists.

Use `Option α` for a nullable field. LeanDB maps `none` to SQL `NULL`.

## Queries

`DbM α` is a database action that returns a value of type `α` or a `DbError`.
The main operations are `select`, `insert`, `update`, and `delete`.

```lean
def drafts : DbM (Array (Stored Note)) :=
  select [Note] (fun note => note.val.status == .draft)
    (.key fun note => note.val.title)
```

The table list determines the row type. `select [Note]` works with
`Stored Note`. Selecting two tables works with a pair of stored rows.
The [tickets example](../examples/tickets/Tickets/Queries.lean) shows joins.

LeanDB builds a typed query plan from the predicate. Supported expressions
become SQL with bound parameters. Other expressions stay in Lean.
The original predicate is always applied to the decoded rows.
Sorting runs in Lean too.

`select` currently returns complete entity rows. You can map those results
to individual fields in Lean. That does not reduce the columns read by SQL.

String predicates push too (LDB-14): `String.startsWith` becomes SQL
`LIKE ? ESCAPE '\'` with the pattern escaped and bound, and
`String.contains` becomes `instr(…) > 0`. Case-insensitive matching is
`icontains` — `instr(lower(…), lower(?)) > 0` — and it is ASCII-only:
SQLite's `lower()` folds ASCII letters unless the ICU extension is
loaded, and Lean's `String.toLower` folds the same way, so the two agree.
An application needing full Unicode case folding should store a folded
shadow column and filter on that. `prefix` uses an index only when the
column's collation agrees with `LIKE`'s ASCII folding: declare the index
`IndexSpec.collate := some .nocase`, and SQLite will serve
`LIKE 'x%'` as an index range.

`log` shows the query plans and their outcomes. Set
`set_option leandb.explain true` to inspect plans during compilation.
Advanced queries can use `Pred`, `pred%`, and `selectP` directly.

## Bases and instances

A base is a Lean package that defines tables and queries. Its `LeanDb.Base`
value lists the tables, registered queries, and optional seed data.

```lean
def base : LeanDb.Base := {
  name := "notes"
  tables := [.of Note]
  queries := [query% drafts]
}

def main (args : List String) : IO UInt32 := Cli.run base args
```

`query%` registers a query for the CLI and server interfaces. It records
the query's name and parameters. `base.specs` derives the schema from the
tables and orders their foreign-key dependencies.

An instance is one SQLite file. The same base can open several instances.
For example, development and production can use different files.
The CLI chooses the file in this order:

1. `--db <path>` before the verb (`--` ends options).
2. The `LEANDB_DB` environment variable.
3. The base's default path, normally `data/<name>.sqlite`.

Another Lean program can import the base and use it directly:

```lean
def readDrafts (path : System.FilePath) :
    IO (Except DbError (Array (Stored Note))) :=
  base.withInstance (Instance.ofPath path) drafts
```

## Reads and writes

LeanDB decodes stored columns before returning entity values. Bad data
produces an error naming the table and field.
JSON input passes through the same field codecs.

`insert` returns the saved row with its assigned ID. `update` compares the
stored row with the old value before writing the new one. A conflicting
change returns `stale`. Deleting a referenced row returns `restricted`.

Types check the values passed to these operations. Database state still
needs runtime checks. A typed reference, for example, can name a row that
has already been deleted.

## Schema changes

LeanDB records a schema fingerprint in each instance. It checks that the
instance matches the base before running data operations.
A mismatch requires a migration.

Without a frozen history, LeanDB compares the stored schema with the code.
It plans changes such as adding a table or an optional column. Changes
that need a custom row conversion are refused.

`migrate freeze` saves schema versions as Lean source. A migration can then
use `Step.transformT` with a function of type `Old → Except String New`.
Lean checks the input and output types. The function can reject a row.
If it does, that migration rolls back.

Run `migrate status` to review a plan and its query impact. Run
`migrate apply` to apply it. Each version runs in a transaction and gets a
backup by default. Destructive changes require `--allow-destructive`.
`migrate rollback` restores the last migration backup, including its data.
Writes made after that backup are not retained by the restore.

The [legacy example](../examples/legacy/README.md) shows a complete frozen
migration. Package versions such as `0.3.1` are separate from an instance's
schema version.

## Existing databases and other applications

`leandb import-sqlite` generates a base from an existing SQLite schema.
It does not automatically adopt the source file as the new base's instance.
Follow the generated instructions to choose or copy the instance file.
Review `IMPORT.md` and `import-report.json` for features it cannot preserve.

A base can expose its tables and queries over JSON lines, HTTP, or MCP.
`client%` creates a typed client stub from a registered query definition.
Clients check the server's schema fingerprint before using the base.
The [dashboard example](../examples/dashboard/Main.lean) shows local,
stdio, and HTTP calls. HTTP clients use the separate `leandb-http` adapter.

See the [CLI reference](../README.md#the-cli-every-base-gets) for commands.
