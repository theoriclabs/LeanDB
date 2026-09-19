import SQLite
import Lean.Data.Json
import LeanDb.Entity
import LeanDb.Derive

namespace LeanDb.Import

/-! # `leandb import-sqlite` — generate a typed base from an existing SQLite file

Introspects an existing SQLite database (`sqlite_master`, `PRAGMA
table_info`, `PRAGMA foreign_key_list`, `PRAGMA index_list` and `PRAGMA
index_info`) and generates a complete base package: validated newtypes per
text column ("import loose, tighten forever"), `Ref` for single-column FKs
onto INTEGER-PRIMARY-KEY row keys, `Option` for nullable columns.

Partial SQL support is a stated non-concern (plan.md §5.3) — *silent*
partiality is not. Everything not carried (views, triggers, indexes,
CHECKs, skipped tables and columns) lands by name with a reason in
`IMPORT.md` and `import-report.json`.
-/

open Lean (Json)

/-! ## Introspection -/

structure RawColumn where
  name : String
  declType : String
  notnull : Bool
  /-- 1-based position within the primary key; 0 when not part of it. -/
  pkIndex : Nat
  defaultSql : Option String
  deriving Repr, Inhabited

structure RawFk where
  groupId : Nat
  fromCol : String
  toTable : String
  /-- `none` means the FK targets the parent's primary key implicitly. -/
  toCol : Option String
  onUpdate : String
  onDelete : String
  matchClause : String
  deriving Repr, Inhabited

/-- One row of `PRAGMA index_list`, plus its `PRAGMA index_info` columns.
    This is the authoritative source for UNIQUE constraints — far better
    than scanning the `CREATE TABLE` text, which cannot tell a constraint
    from a column named `unique_ref`. -/
structure RawIndex where
  name : String
  isUnique : Bool
  /-- `origin`: `"u"` a UNIQUE clause, `"pk"` the primary key, `"c"` a
      `CREATE INDEX`. Empty on SQLite too old to report it — treated as
      unknown, i.e. still reported. -/
  origin : String
  isPartial : Bool
  /-- Indexed columns in order; `none` for an indexed expression. -/
  columns : Array (Option String)
  deriving Repr, Inhabited

structure RawTable where
  name : String
  createSql : String
  columns : Array RawColumn
  fks : Array RawFk
  indexes : Array RawIndex
  deriving Repr, Inhabited

structure RawSchema where
  tables : Array RawTable
  views : Array String
  triggers : Array String
  indexes : Array String
  deriving Repr, Inhabited

private def quoteIdent (s : String) : String :=
  "\"" ++ s.foldl (fun acc c => if c == '"' then acc ++ "\"\"" else acc.push c) "" ++ "\""

private def collectRows (db : SQLite) (sql : String) (read : SQLite.Stmt → IO α) :
    IO (Array α) := do
  let stmt ← db.prepare sql
  let mut out := #[]
  repeat
    if ← stmt.step then out := out.push (← read stmt) else break
  return out

/-- Read the source database's structure. Read-only: nothing is written. -/
def introspect (path : System.FilePath) : IO RawSchema := do
  let db ← SQLite.open path
  let master ← collectRows db
    "SELECT type, name, COALESCE(sql, '') FROM sqlite_master ORDER BY rowid"
    fun stmt => do
      let ty ← stmt.columnText 0
      let name ← stmt.columnText 1
      let sql ← stmt.columnText 2
      pure (ty, name, sql)
  let mut tables := #[]
  let mut views := #[]
  let mut triggers := #[]
  let mut indexes := #[]
  for (ty, name, sql) in master do
    if name.startsWith "sqlite_" then
      continue
    if ty == "table" then
      if name.startsWith "_leandb_" then
        continue
      let columns ← collectRows db s!"PRAGMA table_info({quoteIdent name})" fun stmt => do
        let cname ← stmt.columnText 1
        let decl ← stmt.columnText 2
        let notnull ← stmt.columnInt64 3
        let defaultSql ← do
          match ← stmt.columnType 4 with
          | .null => pure none
          | _ => some <$> stmt.columnText 4
        let pk ← stmt.columnInt64 5
        pure { name := cname, declType := decl, notnull := notnull != 0,
               pkIndex := pk.toNatClampNeg, defaultSql : RawColumn }
      let fks ← collectRows db s!"PRAGMA foreign_key_list({quoteIdent name})" fun stmt => do
        let gid ← stmt.columnInt64 0
        let toTable ← stmt.columnText 2
        let fromCol ← stmt.columnText 3
        let toCol ← do
          match ← stmt.columnType 4 with
          | .null => pure none
          | _ => some <$> stmt.columnText 4
        let onUpdate ← stmt.columnText 5
        let onDelete ← stmt.columnText 6
        let matchClause ← stmt.columnText 7
        pure { groupId := gid.toNatClampNeg, fromCol, toTable, toCol,
               onUpdate, onDelete, matchClause : RawFk }
      -- Collect the index rows first: `index_info` needs its own statement
      -- per index, so the outer cursor must be exhausted before we recurse.
      let indexList ← collectRows db s!"PRAGMA index_list({quoteIdent name})"
        fun stmt => do
          let iname ← stmt.columnText 1
          let uniq ← stmt.columnInt64 2
          let origin ← stmt.columnText 3
          let part ← stmt.columnInt64 4
          pure (iname, uniq != 0, origin, part != 0)
      let mut tblIndexes : Array RawIndex := #[]
      for (iname, isUnique, origin, isPartial) in indexList do
        let cols ← collectRows db s!"PRAGMA index_info({quoteIdent iname})"
          fun stmt => do
            -- An indexed expression has a NULL column name.
            match ← stmt.columnType 2 with
            | .null => pure none
            | _ => some <$> stmt.columnText 2
        tblIndexes := tblIndexes.push { name := iname, isUnique, origin,
                                        isPartial, columns := cols }
      tables := tables.push { name, createSql := sql, columns, fks,
                              indexes := tblIndexes }
    else if ty == "view" then
      views := views.push name
    else if ty == "trigger" then
      triggers := triggers.push name
    else if ty == "index" then
      indexes := indexes.push name
  return { tables, views, triggers, indexes }

/-! ## Name mangling -/

private def hasSub (s sub : String) : Bool := (s.splitOn sub).length > 1

private def upperStr (s : String) : String :=
  s.foldl (fun acc c => acc.push c.toUpper) ""

private def capitalize (s : String) : String :=
  (s.foldl (init := ("", true)) fun (acc, first) c =>
    (acc.push (if first then c.toUpper else c), false)).1

/-- `"user_profile"` → `"UserProfile"`; `none` when a segment is empty. -/
private def upperCamelOf (snake : String) : Option String :=
  let segs := snake.splitOn "_"
  if segs.any (·.isEmpty) then none
  else some (segs.foldl (fun acc seg => acc ++ capitalize seg) "")

private def isValidStructName (s : String) : Bool :=
  !s.isEmpty &&
  (s.foldl (init := (true, true)) fun (ok, first) c =>
    (ok && (if first then c.isUpper && c.isAlpha else c.isAlpha || c.isDigit), false)).1

/-- Lean names the generated code must never claim: core and engine types
    the generated files mention (or could shadow disastrously). -/
private def blockedNames : List String :=
  ["Option", "Id", "Ref", "Stored", "Entity", "ColCodec", "Col", "SqlType",
   "TableSpec", "ColumnSpec", "DbError", "Int", "Int64", "Int32", "Nat",
   "String", "Float", "Bool", "Array", "List", "Except", "Sum", "Prod",
   "Unit", "Char", "Type", "Prop", "IO", "Json", "Main", "Repr", "Ord",
   "BEq", "Hashable", "DecidableEq", "SQLite", "LeanDb", "Lean"]

/-- The struct name for a table: must round-trip through
    `LeanDb.Derive.tableNameOf` (the deriving machinery's only notion of a
    table name), be a valid Lean identifier, and not claim a core name. -/
def structNameFor (table : String) : Except String String := do
  let some cand := upperCamelOf table
    | .error s!"table name {String.quote table} cannot be mangled to a Lean struct name (empty snake_case segment)"
  unless isValidStructName cand do
    .error s!"table name {String.quote table} does not mangle to a valid Lean identifier ({String.quote cand})"
  unless Derive.tableNameOf (Lean.Name.mkSimple cand) == table do
    .error s!"struct name {String.quote cand} does not round-trip to {String.quote table} through LeanDb.Derive.tableNameOf"
  if blockedNames.contains cand then
    .error s!"struct name {String.quote cand} collides with a core/engine name"
  return cand

private def isValidFieldName (s : String) : Bool :=
  !s.isEmpty &&
  (s.foldl (init := (true, true)) fun (ok, first) c =>
    (ok && (if first then c.isAlpha else c.isAlpha || c.isDigit || c == '_'), false)).1

/-- Lean keywords that are still fine as field names inside guillemets. -/
private def leanKeywords : List String :=
  ["at", "by", "calc", "do", "else", "end", "for", "fun", "have", "if", "in",
   "let", "match", "then", "with", "where", "from", "import", "open",
   "mutual", "namespace", "section", "structure", "inductive", "instance",
   "class", "def", "theorem", "lemma", "example", "axiom", "abbrev",
   "opaque", "variable", "universe", "deriving", "extends", "macro",
   "notation", "syntax", "set_option", "private", "protected", "partial",
   "unsafe", "noncomputable", "rec", "return", "try", "catch", "finally",
   "throw", "show", "sorry", "admit", "exact", "this", "mut", "break",
   "continue", "while", "repeat", "until", "global", "local", "scoped",
   "attribute", "export", "include", "omit", "exit", "hiding", "renaming",
   "infix", "infixl", "infixr", "prefix", "postfix", "initialize", "nomatch",
   "fine", "when", "unless"]

/-- Render a column name as a Lean field binder (keywords get guillemets). -/
private def renderFieldName (s : String) : String :=
  if leanKeywords.contains s then s!"«{s}»" else s

/-- Column name → segment of a scalar newtype name (best effort; the result
    is deduplicated against everything else in the plan). -/
private def camelizeColumn (col : String) : String :=
  let cleaned := col.foldl (fun acc c =>
    acc.push (if c.isAlpha || c.isDigit then c else '_')) ""
  let segs := (cleaned.splitOn "_").filter (!·.isEmpty)
  let joined := segs.foldl (fun acc seg => acc ++ capitalize seg) ""
  if joined.isEmpty then "Column" else joined

/-! ## Lexically-aware scanning of stored DDL

SQLite has no pragma for CHECK constraints, so they can only come from the
stored `CREATE TABLE` text. A bare substring search over that text invents
constraints for a column named `check_digit`, for `CHECK` inside a string
default or a quoted identifier, or inside a comment — `sqlite_master.sql`
keeps comments verbatim. These helpers tokenize instead: quoted runs and
comments yield nothing, so nothing inside them can pass for a keyword.

This is deliberately *not* a SQL parser. It answers one question — does
this bare word appear as a token here — and anything it cannot resolve
stays reported. -/

/-- SQLite identifier body characters. Used to require whole-token matches,
    so `check_digit` never reads as `CHECK`. -/
private def isIdentChar (c : Char) : Bool :=
  c.isAlpha || c.isDigit || c == '_' || c == '$'

/-- Skip past the closing `q`; a doubled `q` is the SQL escape, not a close.
    An unterminated run swallows the rest, which is what SQLite would do. -/
private partial def skipQuoted (q : Char) : List Char → List Char
  | [] => []
  | [c] => if c == q then [] else []
  | c :: c' :: rest =>
      if c == q then (if c' == q then skipQuoted q rest else c' :: rest)
      else skipQuoted q (c' :: rest)

private partial def skipBlockComment : List Char → List Char
  | [] => []
  | '*' :: '/' :: rest => rest
  | _ :: rest => skipBlockComment rest

private partial def bareWordsAux : List Char → Array String → Array String
  | [], acc => acc
  | '-' :: '-' :: rest, acc => bareWordsAux (rest.dropWhile (· != '\n')) acc
  | '/' :: '*' :: rest, acc => bareWordsAux (skipBlockComment rest) acc
  | '\'' :: rest, acc => bareWordsAux (skipQuoted '\'' rest) acc
  | '"' :: rest, acc => bareWordsAux (skipQuoted '"' rest) acc
  | '`' :: rest, acc => bareWordsAux (skipQuoted '`' rest) acc
  -- `[...]` identifiers have no escape: the first `]` closes.
  | '[' :: rest, acc => bareWordsAux ((rest.dropWhile (· != ']')).drop 1) acc
  | c :: rest, acc =>
      if isIdentChar c then
        let word := String.ofList (c :: rest.takeWhile isIdentChar)
        bareWordsAux (rest.dropWhile isIdentChar) (acc.push word)
      else bareWordsAux rest acc

/-- Bare word tokens of some SQL, in order, original case. Text inside
    string literals, quoted identifiers and comments is not represented. -/
private def bareWords (sql : String) : Array String :=
  bareWordsAux sql.toList #[]

/-- The CHECK constraints of a stored `CREATE TABLE`, in source order; the
    payload is the `CONSTRAINT <name>` label where the source gave one.
    `CHECK` is reserved in SQLite, so a bare `CHECK` token in a table
    definition is always a constraint — an identifier spelled that way has
    to be quoted, and quoted text never reaches here. -/
private def checkConstraintsIn (createSql : String) : Array (Option String) :=
  _root_.Id.run do
    let ws := bareWords createSql
    let mut out : Array (Option String) := #[]
    for i in [0:ws.size] do
      if upperStr ws[i]! == "CHECK" then
        out := out.push <|
          if i ≥ 2 && upperStr ws[i - 2]! == "CONSTRAINT" then some ws[i - 1]!
          else none
    return out

/-! ## The import plan -/

inductive Mapping where
  | int64
  | float
  | ref (table structName : String)
  | newtype (name : String)
  deriving Repr, Inhabited, DecidableEq

def Mapping.describe : Mapping → String
  | .int64 => "Int64"
  | .float => "Float"
  | .ref _ s => s!"Ref {s}"
  | .newtype n => s!"newtype {n} (raw String, identity validator)"

structure FieldPlan where
  column : String
  declType : String
  nullable : Bool
  mapping : Mapping
  notes : Array String := #[]
  deriving Repr, Inhabited

structure TablePlan where
  table : String
  structName : String
  fields : Array FieldPlan
  skippedColumns : Array (String × String) := #[]
  notes : Array String := #[]
  deriving Repr, Inhabited

structure NotCarried where
  kind : String
  name : String
  reason : String
  deriving Repr, Inhabited

structure Plan where
  baseName : String
  moduleName : String
  /-- Imported tables in FK-dependency (topological) order. -/
  tables : Array TablePlan
  skippedTables : Array (String × String)
  notCarried : Array NotCarried
  notes : Array String
  deriving Repr, Inhabited

/-- Eligibility: single INTEGER PRIMARY KEY rowid alias named `id`,
    a mangleable name, and identifier-safe columns. -/
private def eligibilityOf (t : RawTable) : Except String String := do
  if hasSub (upperStr t.createSql) "WITHOUT ROWID" then
    .error "WITHOUT ROWID tables have no rowid for LeanDB's `id`"
  let pks := t.columns.filter (·.pkIndex > 0)
  if pks.size == 0 then
    .error "no primary key; LeanDB requires an INTEGER PRIMARY KEY rowid alias named `id`"
  if pks.size > 1 then
    let names := String.intercalate ", " (pks.toList.map (·.name))
    .error s!"composite primary key ({names}); LeanDB requires a single INTEGER PRIMARY KEY rowid alias"
  let pk := pks[0]!
  unless upperStr pk.declType == "INTEGER" do
    .error s!"primary key {String.quote pk.name} is declared {String.quote pk.declType}, not INTEGER — not a rowid alias"
  unless pk.name == "id" do
    .error s!"primary key column is named {String.quote pk.name}, not \"id\"; the engine addresses rows via `id`"
  for c in t.columns do
    if c.pkIndex == 0 && !isValidFieldName c.name then
      .error s!"column {String.quote c.name} is not a valid Lean identifier"
  structNameFor t.name

private structure Eligible where
  raw : RawTable
  structName : String

/-- Map one non-pk column. `.newtype ""` is a placeholder filled in by the
    naming pass; refs may still be downgraded by the cycle pass. -/
private def mapColumn (eligibleNames : Array (String × String))
    (skippedNames : Array String) (t : RawTable) (c : RawColumn) :
    Except (String × String) FieldPlan := do  -- .error = (column, skip reason)
  let declU := upperStr c.declType
  let mut notes : Array String := #[]
  -- FK lookup: only single-column FK groups are Ref candidates.
  let fk? := t.fks.find? (·.fromCol == c.name)
  let isComposite := fk?.elim false fun fk => (t.fks.filter (·.groupId == fk.groupId)).size > 1
  -- a name the generated symbol inductive cannot declare (`rec` collides
  -- with its recursor, the modifier keywords cannot start a constructor):
  -- importing it would produce a package that fails to compile with an
  -- unattributed kernel or parser error
  if LeanDb.Derive.unusableSymNames.contains c.name then
    .error (c.name, s!"column name {String.quote c.name} cannot be declared as a Lean field \
symbol (an inductive constructor with that name is refused by Lean); column skipped")
  if hasSub declU "BLOB" then
    let extra := if c.notnull && c.defaultSql.isNone then
      " (NOT NULL without default: inserts through LeanDB will be rejected by SQLite)" else ""
    .error (c.name, s!"BLOB columns are unsupported; column skipped{extra}")
  let mapping ← do
    if hasSub declU "INT" then
      match fk? with
      | some fk =>
          if isComposite then
            notes := notes.push s!"part of a composite FK to {fk.toTable}; imported as Int64, reference not typed"
            pure Mapping.int64
          else if fk.toCol != none && fk.toCol != some "id" then
            notes := notes.push s!"FK references {fk.toTable}({fk.toCol.getD ""}), not the row key; imported as Int64"
            pure Mapping.int64
          else
            match eligibleNames.find? (·.1 == fk.toTable) with
            | some (_, sname) => pure (Mapping.ref fk.toTable sname)
            | none =>
                if skippedNames.contains fk.toTable then
                  notes := notes.push s!"FK to skipped table {String.quote fk.toTable}; imported as Int64"
                else
                  notes := notes.push s!"FK to unknown table {String.quote fk.toTable}; imported as Int64"
                pure Mapping.int64
      | none => pure Mapping.int64
    else if hasSub declU "CHAR" || hasSub declU "CLOB" || hasSub declU "TEXT" then
      pure (Mapping.newtype "")
    else if hasSub declU "REAL" || hasSub declU "FLOA" || hasSub declU "DOUB" then
      pure Mapping.float
    else if hasSub declU "NUMERIC" || hasSub declU "DECI" then
      notes := notes.push s!"declared type {String.quote c.declType} (NUMERIC affinity) imported as Float"
      pure Mapping.float
    else if c.declType.isEmpty then
      notes := notes.push "no declared type; imported as a raw TEXT newtype — non-TEXT stored values will fail to decode"
      pure (Mapping.newtype "")
    else
      notes := notes.push s!"unrecognized declared type {String.quote c.declType}; imported as a raw TEXT newtype — non-TEXT stored values will fail to decode"
      pure (Mapping.newtype "")
  if let some fk := fk? then
    if !(hasSub declU "INT") then
      notes := notes.push s!"FK to {fk.toTable} on a non-INTEGER column; reference not typed"
    if fk.onDelete != "RESTRICT" || fk.onUpdate != "RESTRICT" || fk.matchClause != "NONE" then
      notes := notes.push s!"source FK actions are ON DELETE {fk.onDelete}, ON UPDATE {fk.onUpdate}, MATCH {fk.matchClause}; the adopted file keeps them, while a future LeanDB table rebuild normalizes the typed FK to RESTRICT"
  return { column := c.name, declType := c.declType, nullable := !c.notnull, mapping, notes }

/-- Build the import plan: eligibility, column mapping, topological order
    with cycle downgrades, scalar newtype naming. Pure. -/
def planOf (baseName moduleName : String) (raw : RawSchema) : Plan := _root_.Id.run do
  -- Phase 1: eligibility + struct names.
  let mut skippedTables : Array (String × String) := #[]
  let mut eligible : Array Eligible := #[]
  for t in raw.tables do
    match eligibilityOf t with
    | .error reason => skippedTables := skippedTables.push (t.name, reason)
    | .ok sname => eligible := eligible.push ⟨t, sname⟩
  let eligibleNames := eligible.map (fun e => (e.raw.name, e.structName))
  let skippedNames := skippedTables.map (·.1)
  -- Phase 2: column mapping.
  let mut plans : Array TablePlan := #[]
  for e in eligible do
    let mut fields : Array FieldPlan := #[]
    let mut skippedCols : Array (String × String) := #[]
    let mut tnotes : Array String := #[]
    for c in e.raw.columns do
      if c.pkIndex > 0 then
        continue
      match mapColumn eligibleNames skippedNames e.raw c with
      | .error (col, reason) => skippedCols := skippedCols.push (col, reason)
      | .ok f => fields := fields.push f
    plans := plans.push { table := e.raw.name, structName := e.structName,
                          fields, skippedColumns := skippedCols, notes := tnotes }
  -- Phase 3: topological order by Ref dependency; cycles are cut by
  -- downgrading the cycle-closing Ref to Int64 (with a note).
  let mut remaining := plans
  let mut ordered : Array TablePlan := #[]
  for _ in [0:plans.size] do
    if remaining.isEmpty then
      break
    let done := ordered.map (·.table)
    let ready? := remaining.find? fun tp =>
      tp.fields.all fun f =>
        match f.mapping with
        | .ref target _ => done.contains target
        | _ => true
    match ready? with
    | some tp =>
        ordered := ordered.push tp
        remaining := remaining.filter (·.table != tp.table)
    | none =>
        -- Cycle: cut at the first remaining table (declaration order).
        let tp := remaining[0]!
        let cut := tp.fields.map fun f =>
          match f.mapping with
          | .ref target _ =>
              if done.contains target then f
              else
                let note := s!"FK to {String.quote target} closes a dependency cycle; imported as Int64"
                { f with mapping := Mapping.int64, notes := f.notes.push note }
          | _ => f
        ordered := ordered.push { tp with fields := cut }
        remaining := remaining.filter (·.table != tp.table)
  -- Phase 4: scalar newtype names, deduplicated against everything.
  let mut taken : Array String :=
    ((blockedNames.toArray) ++ ordered.map (·.structName)).push moduleName
  let mut named : Array TablePlan := #[]
  for tp in ordered do
    let mut fields : Array FieldPlan := #[]
    for f in tp.fields do
      match f.mapping with
      | .newtype _ =>
          let mut cand := tp.structName ++ camelizeColumn f.column
          for _ in [0:taken.size + 1] do
            if taken.contains cand then cand := cand ++ "Col" else break
          taken := taken.push cand
          fields := fields.push { f with mapping := .newtype cand }
      | _ => fields := fields.push f
    named := named.push { tp with fields }
  -- Features not carried, by name, with reasons.
  let mut notCarried : Array NotCarried := #[]
  for v in raw.views do
    notCarried := notCarried.push ⟨"view", v,
      "views are not imported; it remains in the adopted database file but is invisible to the typed layer"⟩
  for tr in raw.triggers do
    notCarried := notCarried.push ⟨"trigger", tr,
      "triggers are not imported; it remains in the adopted database file and will still fire inside SQLite"⟩
  for ix in raw.indexes do
    -- A UNIQUE index carries a constraint, not just a lookup structure;
    -- calling it "an index" would under-report what is being dropped.
    let uniq := raw.tables.any fun t =>
      t.indexes.any fun i => i.name == ix && i.isUnique
    notCarried := notCarried.push ⟨"index", ix,
      "indexes are not represented in the generated schema (no @[index] emission yet); the physical index remains in the adopted database file"
      ++ (if uniq then " — note this one is UNIQUE, a constraint the typed layer does not enforce" else "")⟩
  for t in raw.tables do
    for c in t.columns do
      if let some dflt := c.defaultSql then
        notCarried := notCarried.push ⟨"default", s!"{t.name}.{c.name}",
          s!"SQLite default {String.quote dflt} is not lifted into the generated field; inserts must supply the field, and a future LeanDB rebuild will not preserve this source default"⟩
    for fk in t.fks do
      if fk.onDelete != "RESTRICT" || fk.onUpdate != "RESTRICT" || fk.matchClause != "NONE" then
        notCarried := notCarried.push ⟨"foreign-key action", s!"{t.name}.{fk.fromCol}",
          s!"source uses ON DELETE {fk.onDelete}, ON UPDATE {fk.onUpdate}, MATCH {fk.matchClause}; the adopted file retains those actions, but LeanDB rebuilds emit RESTRICT"⟩
    for ix in t.indexes do
      -- `origin` is authoritative: "pk" is the primary key (carried as the
      -- row key, or the whole table is already skipped) and "c" is a
      -- CREATE INDEX, reported above by name. Anything else — "u", or an
      -- origin this SQLite did not report — is a UNIQUE clause we drop.
      if ix.isUnique && ix.origin != "pk" && ix.origin != "c" then
        let cols := String.intercalate ", "
          (ix.columns.toList.map (·.getD "<expression>"))
        let part := if ix.isPartial then " partial" else ""
        notCarried := notCarried.push
          ⟨"unique constraint", s!"{t.name}({cols})",
           s!"the UNIQUE constraint on ({cols}) is not represented in the generated schema; it stays enforced by SQLite inside the adopted file (backing{part} index {ix.name}), but a future LeanDB rebuild will not preserve it"⟩
  for t in raw.tables do
    -- No pragma exposes CHECKs, so this one is textual; see `bareWords`.
    let checks := checkConstraintsIn t.createSql
    for check in checks do
      if let some cname := check then
        notCarried := notCarried.push ⟨"check", s!"{t.name}.{cname}",
          s!"CHECK constraint {String.quote cname} is not lifted into a smart constructor; it stays enforced by SQLite inside the adopted file (detected by scanning the stored CREATE TABLE — SQLite exposes no pragma for CHECKs)"⟩
    let anon := (checks.filter (·.isNone)).size
    if anon > 0 then
      notCarried := notCarried.push ⟨"check", t.name,
        s!"{anon} unnamed CHECK constraint(s) in the table definition are not lifted into smart constructors; they stay enforced by SQLite inside the adopted file (detected by scanning the stored CREATE TABLE — SQLite exposes no pragma for CHECKs)"⟩
  let notes := #[
    "Import loose, tighten forever: every text column is a named newtype with an identity validator — tighten `make` when you know the rule.",
    "On first open the engine creates `_leandb_meta` inside the adopted file and stores the schema fingerprint; this is expected.",
    "The engine's DDL is CREATE TABLE IF NOT EXISTS — a no-op on the adopted tables; existing data is read through the generated codecs."]
  return { baseName, moduleName, tables := named, skippedTables, notCarried, notes }

/-! ## Code generation (pure: relative path → file contents) -/

private def genHeader : String :=
  "/- Generated by `leandb import-sqlite`. Edit freely — this file is yours\n" ++
  "   now; the importer never regenerates over it. -/\n"

private def renderFieldType (f : FieldPlan) : String :=
  let base := match f.mapping with
    | .int64 => "Int64"
    | .float => "Float"
    | .ref _ sname => s!"LeanDb.Ref {sname}"
    | .newtype n => n
  if f.nullable then
    if hasSub base " " then s!"Option ({base})" else s!"Option {base}"
  else base
/-- The SQLite affinity of a declared type, following the type rules at
    https://www.sqlite.org/datatype3.html (`INT` → INTEGER; `CHAR`/`CLOB`/
    `TEXT` → TEXT; `BLOB` or empty → BLOB; `REAL`/`FLOA`/`DOUB` → REAL;
    else NUMERIC). Generated Lean renders a column's declared type *only*
    as this fixed-vocabulary label: the raw declared type is interpolated
    verbatim into nothing that the Lean compiler parses, because SQLite
    lets a quoted identifier carry arbitrary text as the declared type,
    and embedding it in a doc comment once let a payload like
    `x]-/ def pwn : Nat := 137 /-` close the comment and compile as top
    level Lean (issue #65). The raw string stays visible where it is
    inert data — `import-report.json` and `IMPORT.md`, which quote it. -/
private def affinityOf (declType : String) : String :=
  let d := upperStr declType
  if d.isEmpty then "BLOB affinity (no declared type)"
  else if hasSub d "INT" then "INTEGER affinity"
  else if hasSub d "CHAR" || hasSub d "CLOB" || hasSub d "TEXT" then "TEXT affinity"
  else if hasSub d "BLOB" then "BLOB affinity"
  else if hasSub d "REAL" || hasSub d "FLOA" || hasSub d "DOUB" then "REAL affinity"
  else "NUMERIC affinity"

private def scalarsFile (p : Plan) : String := _root_.Id.run do
  let mut decls : Array String := #[]
  for tp in p.tables do
    for f in tp.fields do
      if let .newtype n := f.mapping then
        decls := decls.push <| String.intercalate "\n" [
          s!"/-- `{tp.table}.{f.column}` ({affinityOf f.declType}). Identity validator — tighten here. -/",
          s!"structure {n} where",
          "  raw : String",
          "  deriving Repr, DecidableEq",
          "",
          s!"def {n}.make : String → Except String {n} :=",
          s!"  .ok ∘ {n}.mk",
          "",
          s!"instance : LeanDb.ColCodec {n} :=",
          s!"  LeanDb.ColCodec.via (·.raw) {n}.make"]
  String.intercalate "\n" [
    "import LeanDb",
    "",
    genHeader,
    "/-! # Scalars: one named newtype per imported text column.",
    "",
    "Import loose, tighten forever (plan.md §5.1): each `make` validates",
    "nothing yet; every future validation is one edit away. -/",
    "",
    s!"namespace {p.moduleName}",
    "",
    String.intercalate "\n\n" decls.toList,
    "",
    s!"end {p.moduleName}",
    ""]

private def entitiesFile (p : Plan) : String := _root_.Id.run do
  let mut decls : Array String := #[]
  for tp in p.tables do
    let fields := tp.fields.toList.map fun f =>
      s!"  {renderFieldName f.column} : {renderFieldType f}"
    decls := decls.push <| String.intercalate "\n" <|
      [s!"/-- Imported from table `{tp.table}` (`id` is LeanDB's, not a field). -/",
       s!"structure {tp.structName} where"]
      ++ fields
      ++ ["  deriving Repr, LeanDb.Entity"]
  let specs := p.tables.toList.map (fun tp => s!"LeanDb.Entity.spec {tp.structName}")
  String.intercalate "\n" [
    "import LeanDb",
    s!"import {p.moduleName}.Scalars",
    "",
    genHeader,
    s!"namespace {p.moduleName}",
    "",
    String.intercalate "\n\n" decls.toList,
    "",
    "/-- FK-dependency order: referenced tables first. -/",
    "def schema : List LeanDb.TableSpec :=",
    s!"  [{String.intercalate ", " specs}]",
    "",
    s!"end {p.moduleName}",
    ""]

private def rootFile (p : Plan) : String :=
  String.intercalate "\n" [
    s!"import {p.moduleName}.Scalars",
    s!"import {p.moduleName}.Entities",
    s!"import {p.moduleName}.Base",
    ""]

private def baseFile (p : Plan) (dbPath : String) : String :=
  let tables := p.tables.toList.map (fun tp => s!".of {tp.structName}")
  String.intercalate "\n" [
    s!"import {p.moduleName}.Entities",
    "",
    genHeader,
    s!"/-! The {p.baseName} base as a value: tables (the schema is derived from",
    "them), queries, and the default instance path. Other packages that",
    s!"import `{p.moduleName}` get this value along with the types. -/",
    "",
    s!"namespace {p.moduleName}",
    "",
    "def base : LeanDb.Base := {",
    s!"  name := {String.quote p.baseName}",
    s!"  module := {String.quote p.moduleName}",
    s!"  tables := [{String.intercalate ", " tables}]",
    s!"  defaultDb := some (System.FilePath.mk {String.quote dbPath})",
    "}",
    "",
    s!"end {p.moduleName}",
    ""]

private def mainFile (p : Plan) : String :=
  String.intercalate "\n" [
    s!"import {p.moduleName}",
    "",
    genHeader,
    s!"/-! The {p.baseName} CLI: `LeanDb.Cli.run` over the base value. -/",
    "",
    "def main (args : List String) : IO UInt32 :=",
    s!"  LeanDb.Cli.run {p.moduleName}.base args",
    ""]

private def lakefileFile (p : Plan) (requirePath : String) : String :=
  String.intercalate "\n" [
    s!"name = {String.quote p.baseName}",
    "version = \"0.1.0\"",
    s!"defaultTargets = [{String.quote p.baseName}]",
    "",
    "[[require]]",
    "name = \"leandb\"",
    s!"path = {String.quote requirePath}",
    "",
    "[[lean_lib]]",
    s!"name = {String.quote p.moduleName}",
    "",
    "[[lean_exe]]",
    s!"name = {String.quote p.baseName}",
    "root = \"Main\"",
    ""]

/-! ## Reports -/

private def fieldMappingLine (f : FieldPlan) : String :=
  let ty := if f.nullable then s!"Option of {f.mapping.describe}" else f.mapping.describe
  let notes := if f.notes.isEmpty then "" else
    " — " ++ String.intercalate "; " f.notes.toList
  s!"| `{f.column}` | `{f.declType}` | {ty} |{notes}"

def importMd (p : Plan) (source dbPath : String) : String := _root_.Id.run do
  let mut sections : Array String := #[]
  sections := sections.push <| String.intercalate "\n" [
    s!"# Import report: base `{p.baseName}`",
    "",
    s!"Generated by `leandb import-sqlite` from `{source}`.",
    "",
    "## Adoption",
    "",
    s!"This base opens `{dbPath}` (relative to the working directory) unless",
    s!"`--db <path>` or `$LEANDB_DB` says otherwise. Place the original SQLite",
    s!"file there (e.g. `cp {source} {dbPath}`) — the file is",
    "*adopted*, not converted:",
    "",
    "- On first open the engine writes the schema fingerprint into a new",
    "  `_leandb_meta` table inside the file. This is expected and harmless.",
    "- The engine's DDL runs as `CREATE TABLE IF NOT EXISTS` — a no-op on",
    "  the existing tables; your data is untouched.",
    "- `PRAGMA foreign_keys = ON` is set per connection. The adopted file's",
    "  original FK actions remain authoritative; non-RESTRICT actions are",
    "  listed below because a future LeanDB rebuild normalizes them to RESTRICT.",
    "",
    "**Import loose, tighten forever**: every text column arrived as a named",
    "newtype with an identity `make`. Tighten each `make` in",
    s!"`{p.moduleName}/Scalars.lean` as you learn the real rules — stored data",
    "is re-validated through it on every read."]
  -- Imported tables.
  let mut imported : Array String := #["## Tables imported", ""]
  if p.tables.isEmpty then
    imported := imported.push "(none)"
  for tp in p.tables do
    imported := imported.push <| String.intercalate "\n" <|
      [s!"### `{tp.table}` → `{p.moduleName}.{tp.structName}`",
       "",
       "The `INTEGER PRIMARY KEY` column `id` becomes LeanDB's row identity (not a field).",
       "",
       "| column | declared | imported as |",
       "|---|---|---|"]
      ++ tp.fields.toList.map fieldMappingLine
      ++ tp.skippedColumns.toList.map (fun (c, r) => s!"| `{c}` | — | **skipped** — {r} |")
      ++ (if tp.notes.isEmpty then [] else ["", String.intercalate "\n" (tp.notes.toList.map ("- " ++ ·))])
      ++ [""]
  sections := sections.push (String.intercalate "\n" imported.toList)
  -- Skipped tables.
  let mut skipped : Array String := #["## Tables skipped", ""]
  if p.skippedTables.isEmpty then
    skipped := skipped.push "(none)"
  for (t, r) in p.skippedTables do
    skipped := skipped.push s!"- `{t}` — {r}"
  sections := sections.push (String.intercalate "\n" skipped.toList)
  -- Not carried.
  let mut nc : Array String := #["## Not carried (by name)", "",
    "Partial SQL support is a stated non-concern; *silent* partiality is not.", ""]
  if p.notCarried.isEmpty then
    nc := nc.push "(nothing else found in the source file)"
  for e in p.notCarried do
    nc := nc.push s!"- {e.kind} `{e.name}` — {e.reason}"
  sections := sections.push (String.intercalate "\n" nc.toList)
  sections := sections.push <| String.intercalate "\n" <|
    ["## Notes", ""] ++ p.notes.toList.map ("- " ++ ·)
  return String.intercalate "\n\n" sections.toList ++ "\n"

def reportJson (p : Plan) (source dbPath : String) : Json :=
  let fieldJson := fun (f : FieldPlan) => Json.mkObj [
    ("column", Json.str f.column),
    ("declaredType", Json.str f.declType),
    ("nullable", Json.bool f.nullable),
    ("mapping", Json.str f.mapping.describe),
    ("notes", Json.arr (f.notes.map Json.str))]
  let tableJson := fun (tp : TablePlan) => Json.mkObj [
    ("table", Json.str tp.table),
    ("struct", Json.str s!"{p.moduleName}.{tp.structName}"),
    ("columns", Json.arr (tp.fields.map fieldJson)),
    ("skippedColumns", Json.arr (tp.skippedColumns.map fun (c, r) =>
      Json.mkObj [("column", Json.str c), ("reason", Json.str r)])),
    ("notes", Json.arr (tp.notes.map Json.str))]
  Json.mkObj [
    ("ok", Json.bool true),
    ("base", Json.str p.baseName),
    ("source", Json.str source),
    ("dbPath", Json.str dbPath),
    ("tablesImported", Json.arr (p.tables.map tableJson)),
    ("tablesSkipped", Json.arr (p.skippedTables.map fun (t, r) =>
      Json.mkObj [("table", Json.str t), ("reason", Json.str r)])),
    ("notCarried", Json.arr (p.notCarried.map fun e =>
      Json.mkObj [("kind", Json.str e.kind), ("name", Json.str e.name),
                  ("reason", Json.str e.reason)])),
    ("notes", Json.arr (p.notes.map Json.str))]

/-- The complete generated base: relative path → file contents. Pure. -/
def renderFiles (p : Plan) (requirePath dbPath source toolchain : String) :
    Array (String × String) :=
  #[("lean-toolchain", toolchain ++ "\n"),
    ("lakefile.toml", lakefileFile p requirePath),
    (p.moduleName ++ ".lean", rootFile p),
    (p.moduleName ++ "/Scalars.lean", scalarsFile p),
    (p.moduleName ++ "/Entities.lean", entitiesFile p),
    (p.moduleName ++ "/Base.lean", baseFile p dbPath),
    ("Main.lean", mainFile p),
    ("IMPORT.md", importMd p source dbPath),
    ("import-report.json", (reportJson p source dbPath).pretty ++ "\n")]

end LeanDb.Import
