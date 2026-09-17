import LeanDb
import LeanDb.Import
import LeanDb.Scaffold

/-! # The `leandb` engine CLI

`leandb import-sqlite <file.db> --name <base-name> --out <dir>` generates a
complete typed base package from an existing SQLite file (plan.md §5).
Machine-first: usage on stdout as JSON; errors as JSON on stderr with the
exit codes of `LeanDb/Cli.lean` (0 ok, 2 operational error, 3 usage).
-/

open Lean (Json)
open LeanDb.Import

def usageJson : Json :=
  Json.mkObj [
    ("ok", Json.bool true),
    ("tool", Json.str "leandb"),
    ("usage", Json.arr #[
      Json.str "import-sqlite <file.db> --name <base-name> --out <dir> [--require-path <path-to-leandb>] [--db-path <path>]",
      Json.str "host --port <port> [--bind <host>] [--auth-token <t>] <name>=<exe>[,<arg>,…]…  (serve many bases under /bases/<name>/…)",
      Json.str "new <name> [--out <dir>] (--leandb-path <path> | --leandb-git <url> [--rev <tag>])  (scaffold a standalone base package)",
      Json.str "--help"]),
    ("defaults", Json.mkObj [
      ("require-path", Json.str "../.."),
      ("db-path", Json.str "data/<file.db basename>")])]

def errJson (code msg : String) : Json :=
  Json.mkObj [("ok", Json.bool false), ("code", Json.str code),
    ("message", Json.str msg)]

def usageErr (msg : String) : IO UInt32 := do
  IO.eprintln (errJson "usage" msg).compress
  return 3

def opErr (code msg : String) : IO UInt32 := do
  IO.eprintln (errJson code msg).compress
  return 2

structure ImportArgs where
  file : Option String := none
  name : Option String := none
  out : Option String := none
  requirePath : String := "../.."
  dbPath : Option String := none

partial def parseImportArgs (args : List String) (acc : ImportArgs := {}) :
    Except String ImportArgs :=
  match args with
  | [] => .ok acc
  | "--name" :: v :: rest => parseImportArgs rest { acc with name := some v }
  | "--out" :: v :: rest => parseImportArgs rest { acc with out := some v }
  | "--require-path" :: v :: rest => parseImportArgs rest { acc with requirePath := v }
  | "--db-path" :: v :: rest => parseImportArgs rest { acc with dbPath := some v }
  | a :: rest =>
      if a.startsWith "--" then .error s!"unknown or valueless option {String.quote a}"
      else match acc.file with
        | none => parseImportArgs rest { acc with file := some a }
        | some _ => .error s!"unexpected extra argument {String.quote a}"

/-- Base names are lowercase snake_case so the module name round-trips. -/
def validBaseName (s : String) : Bool :=
  !s.isEmpty &&
  (s.foldl (init := (true, true)) fun (ok, first) c =>
    (ok && (if first then c.isLower && c.isAlpha
            else (c.isAlpha && c.isLower) || c.isDigit || c == '_'), false)).1

def toolchain : String := "leanprover/lean4:v4.33.0"

def runImport (a : ImportArgs) : IO UInt32 := do
  let some file := a.file | return ← usageErr "import-sqlite: missing <file.db>"
  let some name := a.name | return ← usageErr "import-sqlite: missing --name <base-name>"
  let some out := a.out | return ← usageErr "import-sqlite: missing --out <dir>"
  unless validBaseName name do
    return ← usageErr s!"import-sqlite: base name {String.quote name} must be lowercase snake_case ([a-z][a-z0-9_]*)"
  let some moduleName := LeanDb.Import.structNameFor name |>.toOption
    | return ← usageErr s!"import-sqlite: base name {String.quote name} does not mangle to a Lean module name"
  let filePath : System.FilePath := System.FilePath.mk file
  unless (← filePath.pathExists) do
    return ← opErr "not_found" s!"no such file: {file}"
  let dbPath := a.dbPath.getD ("data/" ++ (filePath.fileName.getD "imported.db"))
  try
    let raw ← introspect filePath
    let plan := planOf name moduleName raw
    let files := renderFiles plan a.requirePath dbPath file toolchain
    let outPath := System.FilePath.mk out
    -- Generation is a one-shot handoff. Refuse the whole operation before
    -- writing anything if any target exists; generated files explicitly
    -- invite user edits and must never be clobbered by a second import.
    let mut conflicts : Array String := #[]
    for (rel, _) in files do
      if ← (outPath / System.FilePath.mk rel).pathExists then
        conflicts := conflicts.push rel
    unless conflicts.isEmpty do
      return ← opErr "exists"
        s!"refusing to overwrite existing generated files in {out}: {conflicts.toList}"
    for (rel, contents) in files do
      let p := outPath / System.FilePath.mk rel
      if let some parent := p.parent then
        IO.FS.createDirAll parent
      IO.FS.writeFile p contents
    -- Make the adoption spot exist so `cp <file> <out>/<dbPath>` just works.
    if !System.FilePath.isAbsolute (System.FilePath.mk dbPath) then
      if let some dataDir := (outPath / System.FilePath.mk dbPath).parent then
        IO.FS.createDirAll dataDir
    IO.println (Json.mkObj [
      ("ok", Json.bool true),
      ("base", Json.str name),
      ("out", Json.str out),
      ("source", Json.str file),
      ("dbPath", Json.str dbPath),
      ("imported", Json.arr (plan.tables.map (Json.str ·.table))),
      ("skipped", Json.arr (plan.skippedTables.map fun (t, r) =>
        Json.mkObj [("table", Json.str t), ("reason", Json.str r)])),
      ("files", Json.arr (files.map (Json.str ·.1))),
      ("report", Json.str "IMPORT.md")]).compress
    return (0 : UInt32)
  catch e =>
    opErr "sqlite" (toString e)

structure NewArgs where
  name : Option String := none
  out : Option String := none
  path : Option String := none
  git : Option String := none
  rev : Option String := none

def parseNewArgs : List String → NewArgs → Except String NewArgs
  | [], acc => .ok acc
  | "--out" :: v :: rest, acc => parseNewArgs rest { acc with out := some v }
  | "--leandb-path" :: v :: rest, acc => parseNewArgs rest { acc with path := some v }
  | "--leandb-git" :: v :: rest, acc => parseNewArgs rest { acc with git := some v }
  | "--rev" :: v :: rest, acc => parseNewArgs rest { acc with rev := some v }
  | flag :: _, _ => if flag.startsWith "--" then .error s!"unrecognized flag {flag}" else
      .error s!"unexpected argument {String.quote flag}"

/-- `leandb new`: a standalone base package, requiring the engine from a
    sibling checkout or from git (the pull-out form). Refuses to touch an
    existing file. -/
def runNew (a : NewArgs) : IO UInt32 := do
  let some name := a.name | usageErr "new: a base name is required"
  unless LeanDb.Scaffold.validName name do
    return ← usageErr s!"new: base name must be lowercase snake_case, got {String.quote name}"
  let source ← match a.path, a.git with
    | some p, none =>
      -- `--rev` only means anything to the git form; ignoring it here let
      -- users believe they pinned a revision of a path checkout (issue #69).
      if a.rev.isSome then return ← usageErr "new: --rev applies only to --leandb-git"
      pure (LeanDb.Scaffold.Source.path p)
    | none, some url => pure (LeanDb.Scaffold.Source.git url (a.rev.getD "main"))
    | some _, some _ => return ← usageErr "new: give either --leandb-path or --leandb-git, not both"
    | none, none => return ← usageErr "new: where is the engine? --leandb-path <path> (a checkout) or --leandb-git <url> [--rev <tag>]"
  let target : LeanDb.Scaffold.Target :=
    { name, module := LeanDb.Scaffold.moduleOf name, source, toolchain }
  let out := System.FilePath.mk (a.out.getD name)
  let files := LeanDb.Scaffold.files target
  let mut conflicts : Array String := #[]
  for (rel, _) in files do
    if ← (out / rel).pathExists then conflicts := conflicts.push rel.toString
  unless conflicts.isEmpty do
    return ← opErr "exists" s!"refusing to overwrite existing files in {out}: {conflicts.toList}"
  for (rel, contents) in files do
    let p := out / rel
    if let some parent := p.parent then IO.FS.createDirAll parent
    IO.FS.writeFile p contents
  IO.println (Json.mkObj [("ok", Json.bool true), ("base", Json.str name),
    ("module", Json.str target.module), ("out", Json.str out.toString),
    ("files", Json.arr (files.map fun (rel, _) => Json.str rel.toString).toArray),
    ("next", Json.str s!"cd {out} && lake build && ./.lake/build/bin/{name}_tests")]).compress
  return 0

def main (args : List String) : IO UInt32 := do
  match args with
  | [] | ["help"] | ["--help"] =>
      IO.println usageJson.compress
      return 0
  | "import-sqlite" :: rest =>
      match parseImportArgs rest with
      | .error msg => usageErr s!"import-sqlite: {msg}"
      | .ok a => runImport a
  | "host" :: rest => LeanDb.Host.run rest
  | "new" :: name :: rest =>
      if name.startsWith "--" then usageErr "new: the base name comes first" else
      match parseNewArgs rest { name := some name } with
      | .error msg => usageErr s!"new: {msg}"
      | .ok a => runNew a
  | ["new"] => usageErr "new <name> [--out <dir>] (--leandb-path <path> | --leandb-git <url> [--rev <tag>])"
  | cmd :: _ =>
      usageErr s!"unrecognized command {String.quote cmd}"
