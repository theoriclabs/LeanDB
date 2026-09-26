import LeanDb.Render

namespace LeanDb.Scaffold

/-! # `leandb new`: a base package from nothing

A base is an ordinary Lake package that requires `leandb` — from a
sibling checkout (`--leandb-path`) or from git (`--leandb-git URL --rev
TAG`), which is the pull-out form: the package stands on its own, builds
anywhere, and other projects `require` it in turn. The scaffold is the
README's `notes` base laid out the way the examples are (`Scalars`,
`Enums`, `Entities`, `Queries`, `Seed`, `Base`), with the tests carrying
`leandb_check_head` behind a comment until the schema is first frozen. -/

inductive Source where
  | path (p : String)
  | git (url : String) (rev : String)

structure Target where
  name : String
  module : String
  source : Source
  toolchain : String

private def capitalize (s : String) : String :=
  match s.toList with
  | [] => ""
  | c :: rest => String.ofList (c.toUpper :: rest)

/-- `price_watch` → `PriceWatch`. -/
def moduleOf (name : String) : String :=
  (name.splitOn "_").foldl (fun acc seg => acc ++ capitalize seg) ""

/-- The importer refuses struct names that collide with core/engine names
    (`Import.structNameFor`'s private `blockedNames`, LeanDb/Import.lean);
    the scaffold's module name claims the same names, so the list is
    replicated here — keep the two in sync. `Main` is the load-bearing
    case (issue #69): `leandb new main` mangles to module `Main`, which
    collapses `{module}.lean` (the lib root) and `Main.lean` (the CLI
    entrypoint) onto one path, destroying the aggregate and emitting a
    self-importing package. Refusing is the minimal fix. -/
private def reservedModules : List String :=
  ["Option", "Id", "Ref", "Stored", "Entity", "ColCodec", "Col", "SqlType",
   "TableSpec", "ColumnSpec", "DbError", "Int", "Int64", "Int32", "Nat",
   "String", "Float", "Bool", "Array", "List", "Except", "Sum", "Prod",
   "Unit", "Char", "Type", "Prop", "IO", "Json", "Main", "Repr", "Ord",
   "BEq", "Hashable", "DecidableEq", "SQLite", "LeanDb", "Lean"]

/-- A base name is usable when it is lowercase snake_case AND does not
    mangle to a reserved module name (see `reservedModules`). -/
def validName (s : String) : Bool :=
  !s.isEmpty && s.all (fun c => c.isLower || c.isDigit || c == '_') && (s.get 0).isLower &&
    !reservedModules.contains (moduleOf s)

/-- Escape one character for a TOML basic string: TOML allows only
    `\b \t \n \f \r \" \\` and the `\uXXXX` form — Lean's `String.quote`
    emits `\xNN` for control characters, which every conforming TOML
    parser rejects (issue #70). Keep in sync with `tomlEscapeChar` in
    LeanDb/Import.lean. -/
private def tomlEscapeChar (c : Char) : String :=
  match c.toNat with
  | 0x5c => "\\\\"
  | 0x22 => "\\\""
  | 0x08 => "\\b"
  | 0x09 => "\\t"
  | 0x0a => "\\n"
  | 0x0c => "\\f"
  | 0x0d => "\\r"
  | n => if n < 0x20 || n == 0x7f then
      let hex := Nat.toDigits 16 n
      "\\u" ++ String.mk ((List.replicate (4 - hex.length) '0') ++ hex)
    else String.singleton c

/-- A string as a TOML basic-string literal, valid by construction
    (issue #70). Keep in sync with `tomlString` in LeanDb/Import.lean. -/
def tomlString (s : String) : String :=
  "\"" ++ s.foldl (fun acc c => acc ++ tomlEscapeChar c) "" ++ "\""

private def lakefile (t : Target) : String :=
  let req := match t.source with
    | .path p => s!"path = {tomlString p}"
    | .git url rev => s!"git = {tomlString url}\nrev = {tomlString rev}"
  String.intercalate "\n" [
    s!"name = {tomlString t.name}",
    "version = \"0.1.0\"",
    s!"defaultTargets = [{tomlString t.name}, {tomlString (t.name ++ "_tests")}]",
    "",
    "[[require]]",
    "name = \"leandb\"",
    req,
    "",
    "[[lean_lib]]",
    s!"name = {tomlString t.module}",
    "",
    "[[lean_exe]]",
    s!"name = {tomlString t.name}",
    "root = \"Main\"",
    "",
    "[[lean_exe]]",
    s!"name = {tomlString (t.name ++ "_tests")}",
    s!"root = {tomlString (t.module ++ "Tests")}",
    ""]

private def rootFile (t : Target) : String :=
  String.intercalate "\n" (["Scalars", "Enums", "Entities", "Queries", "Seed", "Base"].map fun m =>
    s!"import {t.module}.{m}") ++ "\n"

private def scalars (t : Target) : String := s!"import LeanDb

/-! # Scalars: validated newtypes. Database and JSON decoding go through
the smart constructor, so a stored value is always a valid one. -/

namespace {t.module}

structure Title where
  raw : String
  deriving Repr, DecidableEq, Ord

def Title.make (s : String) : Except String Title :=
  let t := s.trimAscii.toString
  if t.isEmpty then .error \"title must be nonempty\" else .ok ⟨t⟩

instance : LeanDb.ColCodec Title := LeanDb.ColCodec.via (·.raw) Title.make

end {t.module}
"

private def enums (t : Target) : String := s!"import LeanDb

/-! # Closed worlds: every variant is declared here; the column carries a
CHECK, a `match` in a query compiles to SQL by case-splitting. -/

namespace {t.module}

inductive Status where
  | draft | published
  deriving Repr, DecidableEq, Ord, LeanDb.ClosedEnum

end {t.module}
"

private def entities (t : Target) : String := s!"import LeanDb
import {t.module}.Scalars
import {t.module}.Enums

/-! # Entities: one structure per table; `deriving LeanDb.Entity` derives
the columns, defaults, codecs, JSON, field symbols and migration
metadata. -/

namespace {t.module}

open LeanDb

structure Note where
  title  : Title
  body   : String
  status : Status := .draft
  deriving Repr, LeanDb.Entity

/-- Kept as the hand-written reference the tests compare `base.specs` to. -/
def schema : List TableSpec := [Entity.spec Note]

end {t.module}
"

private def queries (t : Target) : String := s!"import LeanDb
import {t.module}.Entities

/-! # Queries: plain Lean lambdas over `Stored` rows; the plan tactic pushes
what it can to SQL and always re-checks the lambda. -/

namespace {t.module}

open LeanDb

/-- Domain logic the query compiler may unfold into SQL. -/
@[db] def Note.isDraft (n : Note) : Bool := n.status == .draft

def drafts : DbM (Array (Stored Note)) :=
  select [Note] (fun n => n.val.isDraft) (.key (·.val.title.raw))

def byStatus (s : Status) : DbM (Array (Stored Note)) :=
  select [Note] (fun n => n.val.status == s) (.key (·.val.title.raw))

end {t.module}
"

private def seed (t : Target) : String := s!"import LeanDb
import {t.module}.Entities

/-! # Seed: typed inserts through the smart constructors. -/

namespace {t.module}

open LeanDb

def seedM (context : String) (r : Except String α) : DbM α :=
  match r with
  | .ok a => pure a
  | .error msg => throw (.decode \"seed\" context msg)

def seed : DbM Unit := do
  let hello ← seedM \"title\" (Title.make \"Hello\")
  discard <| insert Note \{ title := hello, body := \"first note\" }
  let shipped ← seedM \"title\" (Title.make \"Shipped\")
  discard <| insert Note \{ title := shipped, body := \"went out\", status := .published }

end {t.module}
"

private def baseFile (t : Target) : String := s!"import {t.module}.Entities
import {t.module}.Queries
import {t.module}.Seed

/-! The {t.name} base as a value: tables (the schema is derived from them),
`query%`-derived queries, the seed. Other packages that import
`{t.module}` get this value along with the types and the query defs. -/

namespace {t.module}

open LeanDb LeanDb.Cli

def base : LeanDb.Base := \{
  name := {String.quote t.name}
  module := {String.quote t.module}
  tables := [.of Note]
  queries := [query% drafts, query% byStatus]
  seed := some seed
}

end {t.module}
"

private def mainFile (t : Target) : String := s!"import {t.module}

/-! The {t.name} CLI: `LeanDb.Cli.run` over the base value. -/

def main (args : List String) : IO UInt32 :=
  LeanDb.Cli.run {t.module}.base args
"

private def tests (t : Target) : String := s!"import {t.module}

/-! Tests: the derived schema is the hand-written one; seed and query
against a scratch instance. Once the schema is frozen (`{t.name} migrate
freeze`), uncomment `leandb_check_head` so the build is red until every
schema change is snapshotted. -/

open LeanDb {t.module}

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw <| IO.userError s!\"FAIL: \{message}\"

-- leandb_check_head {t.module}.Migrations.chain {t.module}.base.specs

private def dbPath : System.FilePath := \".lake\" / \"{t.name}_test.sqlite\"

def main : IO UInt32 := do
  check (base.specs == schema) \"Base.specs equals the hand-written schema\"
  if ← dbPath.pathExists then IO.FS.removeFile dbPath
  let inst := Instance.ofPath dbPath
  match ← base.withInstance inst (do seed; drafts) with
  | .ok rows => check (rows.size == 1) s!\"one draft, got \{rows.size}\"
  | .error e => throw <| IO.userError s!\"FAIL: \{e}\"
  IO.println \"{t.name} base: all tests passed\"
  return 0
"

private def readme (t : Target) : String := s!"# {t.name}

A LeanDB base: types (`{t.module}/Scalars.lean`, `Enums.lean`,
`Entities.lean`), queries (`Queries.lean`), seed, and the base value
(`Base.lean`). The instance lives in `data/{t.name}.sqlite` unless
`--db <path>` or `$LEANDB_DB` says otherwise.

```bash
lake build && ./.lake/build/bin/{t.name}_tests
{t.name}=./.lake/build/bin/{t.name}
${t.name} seed
${t.name} query drafts
${t.name} insert note '\{\"title\":\"Third\",\"body\":\"…\"}'
${t.name} serve --http 7411     # or: serve --mcp
```

Change an entity, then `${t.name} migrate status` / `migrate apply`. To
give the base a typed migration history: `${t.name} migrate freeze`,
wire `chain := some {t.module}.Migrations.chain` into the base, and
uncomment `leandb_check_head` in `{t.module}Tests.lean`.
"

private def dockerfile (t : Target) : String := s!"# {t.name} as a container: build the executable, ship only it.
#   docker build -t {t.name} .
#   docker run -p 7411:7411 -v {t.name}-data:/data -e LEANDB_TOKEN=s3cret {t.name}
# The server binds 0.0.0.0 inside the container: set LEANDB_TOKEN before
# publishing the port. The instance lives in the /data volume.

FROM ubuntu:24.04 AS build
ENV DEBIAN_FRONTEND=noninteractive
RUN apt-get update && apt-get install -y --no-install-recommends \\
      curl git ca-certificates build-essential \\
    && rm -rf /var/lib/apt/lists/*
RUN curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \\
    | sh -s -- -y --default-toolchain none
ENV PATH=/root/.elan/bin:$PATH
WORKDIR /src
COPY . .
RUN lake build {t.name}

FROM ubuntu:24.04
RUN apt-get update && apt-get install -y --no-install-recommends ca-certificates libgmp10 curl tzdata \\
    && rm -rf /var/lib/apt/lists/*
COPY --from=build /src/.lake/build/bin/{t.name} /usr/local/bin/base
VOLUME /data
ENV LEANDB_DB=/data/base.sqlite
EXPOSE 7411
HEALTHCHECK --interval=30s --timeout=3s CMD curl -sf http://127.0.0.1:7411/healthz || exit 1
ENTRYPOINT [\"/usr/local/bin/base\"]
CMD [\"serve\", \"--http\", \"7411\", \"--bind\", \"0.0.0.0\"]
"

/-- Every file of the scaffold: relative path → contents. -/
def files (t : Target) : List (System.FilePath × String) :=
  [("lean-toolchain", t.toolchain ++ "\n"),
   ("lakefile.toml", lakefile t),
   (".gitignore", ".lake/\ndata/\n*.sqlite\n"),
   (".dockerignore", ".lake/\ndata/\n*.sqlite\n.git/\n"),
   ("Dockerfile", dockerfile t),
   ("README.md", readme t),
   (s!"{t.module}.lean", rootFile t),
   (s!"{t.module}/Scalars.lean", scalars t),
   (s!"{t.module}/Enums.lean", enums t),
   (s!"{t.module}/Entities.lean", entities t),
   (s!"{t.module}/Queries.lean", queries t),
   (s!"{t.module}/Seed.lean", seed t),
   (s!"{t.module}/Base.lean", baseFile t),
   ("Main.lean", mainFile t),
   (s!"{t.module}Tests.lean", tests t)]

end LeanDb.Scaffold
