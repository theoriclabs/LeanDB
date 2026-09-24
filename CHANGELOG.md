# Changelog

## Unreleased

- **M15-pre.** `DbState` is a lawful `(t : Fin nTables) → Table (pack t).ty`
  with no `unsafe` / `implemented_by` in `LeanDb/Typed`. `get` / `set` /
  `load` are the executed definitions; `get_set_same`, `get_set_other`,
  `empty_rows`, and `insert_team_on_empty` are proved. `Read.get` /
  `lookup` return `Valid α` (invariant proof; coerces to `Stored`);
  `Txn.update` / `append` take that proof plus `Checked` so callers need
  not re-check. `deleteAt` is fueled by `rowCount` (no `partial`).
  `exact_plan` is kernel-reducible (`decide`, not `native_decide`).
  `scripts/CheckAxioms.lean` allowlists `propext` / `Classical.choice` /
  `Quot.sound`. Harness compares production `load` to `denote` through
  lawful `get`.
- **M14c.** Close remaining QUERIES.md §3 / §5 gaps: `patch` writes only
  the named fields (meaning merge and SQL `UPDATE`); `SetError` lists
  only constraints over written fields (`Unique.Touching` /
  `ForeignKey.Within` reduce to `Empty`); window/`first`/`count`/`exists`
  refuse a non-exact plan at elaboration; FK `join` is a SQL `JOIN`;
  decidable `DbState.checkWF` (harness after every successful write);
  `Runtime.Service.runRead` on a reader snapshot and `runTxn` on the
  writer; per-FK `ON DELETE` RESTRICT or CASCADE (`cascade%`), mirrored
  in SQLite, meaning, and `DeleteError.Restricting`. Tests in
  `TestsM14c.lean`. Remaining deviations are listed in
  `docs/typed-interface.md`.
- **M14b.** Typed writes and transaction programs: schema-derived
  `InsertError` / `UpdateError` / `SetError` / `AppendError` /
  `DeleteError`, `Txn σ s ε α` with ST-style `Current σ α`, `Txn.denote`
  and `Txn.run` (`BEGIN IMMEDIATE`, SAVEPOINT per write, constraints
  checked in declaration order), and an execution-equals-meaning harness
  (`LeanDb/Typed/Harness.lean`, `TestsM14b.lean`).
- **LDB-24.** `readSnapshot` is public: a deferred `BEGIN DEFERRED`
  snapshot for multi-statement reads, so adapters need not rebuild one.
- **LDB-23.** `Pred.Snapshot.rows` fails on an undecodable row instead of
  dropping it (which made `forall` vacuously true over corrupt data).
- **LDB-22.** `count` / `exists?` apply the lambda, not only the plan, so
  a residual (or a hand-written `.tt` plan) cannot overcount. `countP` /
  `existsP` still push `COUNT(*)` / `EXISTS` for exact plans.
- **LDB-21.** `patch` refuses a guard that contains an opaque leaf.
  Opaque used to render as true, so a residual false guard still wrote.
- **LDB-20.** Multi-statement verbs that join an outer transaction run
  under a SAVEPOINT, so catching their error and committing cannot keep
  partial effects.
- **LDB-19.** `Runtime.Service.withReader` locks each pooled connection
  and never hands out the writer. `readers := 0` still opens one
  dedicated read-only slot, so a reader cannot write and two callbacks
  cannot share one SQLite handle.
- **LDB-18.** `Nat` columns are bounded to `0 … Int64.maxValue`. Writes
  of a larger `Nat` are `.decode`; a comparison bound outside that range
  renders as a tautology or contradiction instead of wrapping, so
  `select (·.n < 2^64)` agrees with its meaning. `SqlOrd Nat` stays.
- **LDB-17.** `selectP` / `existsP` apply `LIMIT`/`OFFSET` after the
  residual Lean filter unless the plan is exact (and not a join). A
  pushed window on the `approx` superset can no longer hide a later
  matching row (`existsP` false negatives, short pages).
- **LDB-15 (#129).** `append old new`: grow an entity's child lists against
  the value that was read. Only the added child rows are written, at the
  positions after the stored ones; the parent's columns are written under
  `update`'s compare-and-swap. A list that moved on since the read, or a
  parent that did, is `.stale`, in one connection or across processes
  (`BEGIN IMMEDIATE`, backed by the `(parent, position)` UNIQUE index). A
  list that does not continue the stored one is `.notAppend`. `update`'s
  docstring now says plainly that its CAS does not see child lists.
- **LDB-16 (#130).** Entity invariants. `@[leandb_invariant] def T.invariant
  : T → Bool`, declared before `deriving instance LeanDb.Entity for T`, is
  checked on every read (after the child lists are attached) and before
  every write (`insert`, `insertMany`, `update`, `patch`, `append`). A row
  that fails is `.invariant table name`: never returned, never stored. The
  attribute refuses a check declared after `Entity T` exists. The name is
  part of the schema: `TableSpec.invariant`, `schema_json`, the fingerprint
  (`table:invariant=<name>`; unchanged for a table without one), and a
  journaled `restampInvariant` migration step.
- **Freeze (#131).** Frozen snapshots are written with named fields and
  include `indexes` and `invariant`. Since 0.4.0 they were written as
  `⟨name, #[…]⟩`, which does not compile against a three-field
  `TableSpec`. The legacy example's snapshots are updated.
- **Breaking.** `TableSpec` has a fourth field, `invariant`. Code that
  builds one positionally (`⟨name, columns, indexes⟩`) adds `, none`, or
  switches to named fields. New `DbError` constructors: `invariant`,
  `notAppend`.

## 0.4.0 - 2026-09-18

Public transaction combinator, runtime service, and the LeanGD engine
surface (LDB-01 … LDB-11).

- **LDB-01.** `transaction` / `withTransaction` / `untrackedSqlite` and
  `LeanDb.Runtime.Service` land on mainline: `BEGIN IMMEDIATE` at depth 0,
  savepoints when nested, typed `.abort`, poisoned connections after a
  failed `ROLLBACK`, serialized `withConnection` that converts host
  exceptions, `drain`/`resume`/`snapshot`/`restore`/`close`.
- **LDB-02.** `OpenConfig` (`synchronous`, `cache_size`, `mmap_size`,
  `wal_autocheckpoint`, allowlisted `extraPragmas`) plus `LEANDB_*`
  environment overrides. Defaults stay `synchronous=FULL` / 5s busy
  timeout.
- **LDB-03.** `Indexes α` declares indexes and composite UNIQUE
  constraints; they appear in DDL, `schema` JSON, the fingerprint, and
  `migrate` add/drop plans. Child tables get `(parent, position) UNIQUE`.
- **LDB-04.** `selectP` takes a pushed `Order` and `Window` (`LIMIT` /
  `OFFSET`); a Lean-side sort plus a limit is refused. Tie-break is
  `, id ASC`.
- **LDB-05.** `LogConfig.verbs` (`all` / `failuresAndPlans` /
  `failuresOnly` / `none`) and `sampleEvery`; CLI default remains `.all`.
- **LDB-06.** `count` / `countP` / `exists?` / `existsP` push
  `COUNT(*)` / `EXISTS` when the predicate has no residual.
- **LDB-07.** Typed `patch` with a `Pred` guard; `PatchResult` is
  `.updated` / `.notFound` / `.guardFailed`.
- **LDB-08.** `insertMany` and keyset `scan`.
- **LDB-09.** `Runtime.Config.readers` and `Service.withReader`; write
  verbs on a read-only connection return `DbError.readOnly`.
- **LDB-10.** `deriving instance LeanDb.ClosedEnum` / `DbJson` / `Inline`
  works post-hoc on LeanDB-free domain types.
- **LDB-11.** Extra tables in a fingerprinted instance are tolerated;
  `Base.auxiliary` declares FTS5 objects; `searchP` binds `MATCH`.

Also in this release:

- JSON `true`/`false` is accepted only on `Bool` columns; a `Nat`/`Int64`
  INTEGER no longer silently stores 0/1.
- Declared tables that share a name (or the same name after case folding)
  but are not the same spec are refused at open, instead of one entity
  being silently dropped.
- `--db <path>` is taken only before the verb (`--` ends options). A
  usage error no longer creates the instance file.
- Reads take a deferred snapshot (parent + child lists, and `selectP`'s
  snapshot + pushdown). Open sets `journal_mode=WAL` and `busy_timeout`.
- HTTP: tokenless servers are loopback-only; Host/Origin are pinned on a
  loopback bind; JSON-body routes require `Content-Type: application/json`.
- `restore` (and `migrate rollback`, which shares the code path) validates
  its source before touching the instance: a non-SQLite source is refused
  by the SQLite magic header plus `PRAGMA quick_check`, the copy streams
  in bounded 1 MiB chunks instead of reading the whole file into memory,
  and the session connection is swapped only after the renamed file opens
  cleanly. A failed restore no longer destroys the instance file or leaves
  the session silently serving an empty in-memory database.

## Unreleased


## 0.3.1 - 2026-09-14

- Add a core concepts guide, terminology glossary, and current roadmap.
- Simplify the README and add the architecture diagram.
- Replace example CLI transcripts with short usage guides.
- Remove the old proposal directory and update documentation links.
- Remove the Gpus, Kernels, and Pricewatch examples.
- Update release checks for the remaining example packages.
- Include the typed HTTP client integration and pinned dashboard dependency
  added after the 0.3.0 tag.

Lean 4.33.0 and the pinned SQLite dependency are unchanged.

## 0.3.0 - 2026-09-02

LeanDB 0.3.0 separates the engine from the bases and makes a base a
package: a `LeanDb.Base` value in its own library, the instance chosen
at run time, versioned typed migrations with full backups and rollback,
an impact report before every apply, and the same handler served over
JSON lines, HTTP (with a bearer token), MCP, and a multi-base host.
Bases are importable by other Lean projects, in-process or over the
wire, scaffolded standalone by `leandb new`, and deployable from a
Dockerfile. Engine changes in order of landing:

`LeanDb.Client` is transport-neutral: the existing spawned stdio client
is one implementation, and the standalone sibling `leandb-http` package
adds HTTP through the standalone libcurl-FFI `leanhttp` package. The
dashboard runs the same typed `client%` query locally, over stdio, and
over authenticated HTTP, including fingerprint refusal.

Pushdown: comparisons through a validated newtype's projection push when
the projection is the column's encoding (checked by definitional
equality); case splits on captured closed-enum parameters; value/value
guards fold at plan build; `if`/`cond` on columns reify. BLOB columns are
a typed `decode` error naming table and field. Constraint classification
matches extended result codes first and message text case-insensitively.
The importer reports UNIQUE constraints from `PRAGMA index_list`, named
by column list, and detects CHECK token- and quote-aware. `rows --eq`
splits at the first `=`.

Two new bases: `examples/eats` (restaurants; dietary suitability computed
from ingredients, never stored) and `examples/kernels` (GPU kernels with
typed signatures and composition, benches keyed by gpumarket's `Gpu`).

LEP-0002 landed: `deriving LeanDb.Entity` generates field symbols
(`Ticket.Field`) and `select` carries an intrinsically typed plan
`Pred ts` — column references are Lean values indexed by the storage
codec, ordered comparisons require `SqlOrd` at the constructor, the
residual is an `opaque` leaf, `denote` gives every plan a meaning, and
`approx_sound` proves the pushed fragment never excludes a row the lambda
accepts. `PushPred` is gone; every base's logged plan is byte-identical.
`rows --eq` decodes its value through the column's codec.

LEP-0004 landed: `Pred.exists`/`Pred.forall` over a related table,
denoted against a `Snapshot`, rendered as `EXISTS`/`NOT EXISTS`,
covered by `approx_sound`; `selectP` takes a plan as data and `pred%`
reifies a lambda into one. eats' `suitable` is a single query.

LEP-0003 B landed: `deriving LeanDb.DbJson` honours structure defaults;
JSON columns carry a type shape that the fingerprint, `schema_json` and
the migration diff see (additive-with-defaults changes restamp, others
are refused by name); `:= derived expr` columns are recomputed on write
and checked on read. kernels' signature and search columns use them.

LEP-0003 A landed: `EnumSet α` bitmask columns over a closed world —
mask CHECK, open-time drift scan, JSON as an array of names, `Pred.bit`
so membership pushes; kernels' `fuses`.

LEP-0003 C landed: `deriving LeanDb.Inline` — small fixed structures
flatten into prefixed columns with flat field symbols, nested row JSON
(both spellings accepted), split defaults, and full pushdown through the
projection; kernels' `LaunchConfig`/`NumericProps`.

LEP-0003 D landed: a field `ins : List R` with `R` an `Inline` record is
a child table — the derive declares the entity `Parent.Ins` (`parent :
Ref Parent` with `ON DELETE CASCADE`, `position`, the record's fields),
`Entity.children` describes it (`ChildLink`) and `Entity.specs` lists it.
The list is part of the value: every read attaches it (one `IN (…)`
fetch per child table, chunked), `insert`/`update` write it in a
transaction, `delete` cascades. Row JSON nests it as an array of records.
`xs.any f`/`xs.all f` over a child-list field reify to LEP-0004's
`exists`/`forall`. A derived column may read a child list; its check
runs at attach time. `ColumnSpec.cascade`. kernels' `ins`/`outs`.

Pushdown: a captured `Option α` parameter over a closed world case-splits
(`none` and each `some c`), so "filter by X if given" pushes in both the
`isNone ||` and the `match` spelling; `some a == some b` unwraps.

LEP-0005 stage 1 (eats): configurable espresso offers — a finite
configuration type with a validity predicate, typed option patterns, a
price rule with `decide`d lints, a tabulated `offer_price` table, order
lines quoted against it; seven configuration queries and a second test
executable.
Design docs: LEP-0002, the kernels/restaurants stress study, `ROADMAP.md`.

A base is a value: `LeanDb.Base` (tables, `query%` entries, seed, default
instance path) lives in the base's library (`<Base>/Base.lean`) and
`Main.lean` is `LeanDb.Cli.run <Base>.base`. The schema is derived from
the tables (`Base.specs`: dedup, stable dependency order — every
example's fingerprint is unchanged, asserted by each base's tests). The
instance is chosen at run time: `--db <path>` on any command, else
`$LEANDB_DB`, else `data/<name>.sqlite`. `query%` records parameter
names and types (`help` shows them); `seed` is a verb derived from the
base's declared seed (`query seed` still works). The importer generates
the same shape.

One handler: `Base.handle` is the only place argv meets an open instance;
the one-shot CLI and `serve` are two framings of it. `openDb` splits into
`openDbRaw` (file + bookkeeping tables) and `Conn.verify` (fingerprint,
DDL, drift scan); `migrateOn`/`instanceInfoOn` run on a live connection.
A `Session` gates the base's verbs while the instance is drifted, so
`serve` now stays up on a drifted file: `version` and `migrate` answer,
every other verb returns `schema_mismatch` until `["migrate","apply"]`
succeeds in the same session. Exit codes derive from the response's
`code`.

Backups and rolldown: `migrate apply` takes a full copy of the instance
first (`VACUUM INTO`, after a WAL checkpoint) under
`<instance dir>/backups/<base>-v<k>-<time>.sqlite` unless `--no-backup`;
the journal (`_leandb_migrations`, upgraded in place with
`from_version`, `to_version`, `backup`, `note`) names it, and the apply
report carries `from_version`/`to_version`/`backup`. `migrate rollback`
restores the last applied migration's backup (writes made after the
migration are not in it, and the response says so); `restore <file>`
restores any file; `backup` takes one on demand; `migrate history`
lists the journal. A restore swaps the file under a persistent session
and re-verifies, so `serve` supports all of these.

Versioned, typed migrations. `migrate freeze` writes
`<Module>/Migrations/V<n>.lean`: the schema snapshot as data
(`V<n>.schema`), one raw structure per table (the row as stored, so the
old version lives on as a type), and for `n ≥ 1` the migration `M<n>`
whose mechanical steps are diffed at apply time and whose judgments —
every table the diff refuses — are `Step.transformT V<n-1>.T T fun old
=> sorry` holes, each commented with the refusal; the roll-up
`Migrations.lean` defines `chain`. A base with `chain := some …` is in
chain mode: an instance names its version by fingerprint
(`unknown_lineage`, exit 4, when it matches none), `migrate status`
lists each pending version's steps with row counts, destructiveness and
`transform: provided|required|none`, `migrate apply` runs one migration
per transaction after its backup, transforms rewrite rows through the
frozen old entity and the head entity keeping ids (the first `.error`
aborts, naming the row), and the version is the chain index.
`leandb_check_head chain specs` (in the base's tests) fails the build
until the code's schema is the chain's head. An unstamped adopted file
is stamped at the version whose columns it has, not mislabeled as the
head. Rebuilds set `legacy_alter_table` so an adopted file's views do
not block the rename. `examples/legacy` is the worked example: the
imported `orders.qty` became a closed `size` at V1, the transform
encodes the rule the uncarried `big_orders` view held, and
`legacy_tests` adopts the raw fixture, migrates it, rolls it back and
re-applies.

Footprints and impact. The plan tactic records, per declaration, the
tables and columns every reified plan reads and whether a residual
remains; `query%` unions them (following the def's own callees) into
`QueryEntry.footprint`, statically. The log stores each select's plan as
data (`plan`: tables, the `Pred` as JSON, its footprint) and the
registered query it ran under (`query`). `migrate status` now reports
`changed` (the columns the pending change touches), `impact` (each
registered query whose footprint touches them, with the columns and the
number of logged runs that did), and `unregistered_runs` (logged selects
outside any registered query). This is the third report of the thesis:
a vocabulary edit says which queries it reaches, before `apply`.

HTTP: `<base> serve --http <port> [--bind <host>]` serves the base over
HTTP/1.1 on the toolchain's `Std.Http.Server`. Every route is sugar over
the CLI's argv — `GET /schema|version|log`, `GET /tables/:t?eq=k=v&limit=n`,
`GET|PATCH|DELETE /tables/:t/:id`, `POST /tables/:t`,
`GET /query/:q/:args…` or `POST /query/:q {"args":[…]}`, `POST /seed`,
`GET /migrate`, `POST /migrate/apply?allow_destructive=1&backup=0`,
`POST /migrate/rollback`, `GET /migrate/history`, `POST /backup`,
`POST /restore {"file":…}`, and `POST /rpc` with a JSON argv array —
and reaches the same `Base.handle`; the status code derives from the
response `code`. Requests run one at a time behind a mutex (one SQLite
handle). A request carrying `X-LeanDb-Fingerprint` for another schema
is refused with `schema_mismatch` (409).

Importable bases. A project that `require`s a base package gets its
types, its `base` value and its query defs: `Base.withInstance` runs
them in-process against an instance file (with the base's own schema
check), and `LeanDb.Client` runs them over the wire — `Client.connect`
spawns `<base> serve`, shakes hands on the fingerprint (a client
compiled against another schema is refused before it asks), and
`client% f` turns a query def's signature into a `ClientM` stub whose
arguments render through `CliRender` and whose result decodes through
`QueryIn`, so the remote call is typed like the local one;
`Client.argv` sends any argv. `examples/dashboard` is a non-base
project importing `tickets` and `eats`: it seeds and queries both
in-process and checks the remote `slaBreached` against the local one.

Hosting many bases: `leandb host --port <port> <name>=<exe>[,<arg>…]…`
spawns each base in `serve` mode and serves them under
`/bases/<name>/…` with the same routes a base serves alone (`GET
/bases` lists them with fingerprints; the argv is the wire between the
processes). MCP: `<base> serve --mcp` speaks the Model Context Protocol
over stdio with a tool list derived from the base — `rows_<t>`,
`get_<t>`, `insert_<t>`, `update_<t>`, `delete_<t>` per table,
`query_<q>` per registered query with its parameters as the input
schema, plus `schema`, `version`, `log`, `migrate_status`, `seed` — every
call one argv through `Base.handle`, so an agent picks from the list and
cannot invent a query.

`leandb new <name> (--leandb-path <path> | --leandb-git <url> [--rev
<tag>])` scaffolds a standalone base package — the README's notes base
laid out like the examples (Scalars, Enums, Entities, Queries, Seed,
Base, tests with `leandb_check_head` ready to uncomment) — requiring the
engine from a checkout or from git, which is how a base is pulled out
of this repository: it builds anywhere and other projects `require` it
in turn. Refuses to overwrite existing files. The release check
scaffolds one against the checkout, builds it and runs its tests.

Deployable: `serve --http` and `leandb host` take `--auth-token <t>` (or
`$LEANDB_TOKEN`); with a token set every request must carry
`Authorization: Bearer <t>` or gets 401 with `WWW-Authenticate: Bearer`,
except `GET /healthz`, which is always open for orchestrators. A root
`Dockerfile` (`--build-arg BASE=<example>`) builds any example base into
an image that serves on 7411 with the instance in a `/data` volume;
`leandb new` emits the same Dockerfile for a standalone base. Found on
the way: `Std.Http.Server` generates a `Date` header through `Std.Time`,
which needs zoneinfo; in a minimal container every response died before
its first byte. The server now runs with `generateDate := false` (an
API needs no Date) and the images ship `tzdata` anyway.

## 0.2.0 - 2026-08-25

LeanDB 0.2.0 replaces the earlier decision-query prototype with a typed SQLite engine. Entity structures now derive their table schema, codecs, DDL, JSON representation, CLI operations, migration plan, and schema fingerprint from one Lean definition.

The release includes typed row IDs and foreign references, compare-and-swap updates, restricted deletes, closed enums, multi-table selects, safe SQL pushdown, deterministic sorting, schema migrations, query logging, JSON-lines serving, and the `query%` CLI adapter. `leandb import-sqlite` can generate an editable Lean package and an explicit report of source features it could not carry.

Seven standalone bases exercise the engine: tickets, CRM, shop, GPUs, GPU Market, Price Watch, and a generated legacy SQLite import.

Release review also tightened several boundaries:

- UInt16 and UInt32 decoding now rejects the first out-of-range value instead of wrapping to zero.
- Inserts and partial updates reject non-object JSON and unknown fields.
- CLI row IDs and integer filters reject values outside SQLite's Int64 range.
- SQL identifiers and enum literals are escaped correctly.
- Zero-field entities use valid SQLite insert and update statements.
- Invalid schemas and corrupt migration metadata fail before the database is changed.
- Ordered predicate pushdown is limited to codecs that preserve Lean ordering in SQLite.
- The SQLite importer refuses to overwrite generated files and reports source defaults and foreign-key actions that a later table rebuild would not preserve.
