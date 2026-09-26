import LeanDb.Core

namespace LeanDb.Render

/-! # Rendering Lean source

Shared by the importer (`import-sqlite`) and `migrate freeze`: identifier
hygiene and the literal forms of `Col`, `ColumnSpec` and `TableSpec`, so a
schema snapshot is ordinary Lean data that the compiler re-checks. -/

def leanKeywords : List String :=
  ["at", "by", "do", "end", "for", "from", "fun", "have", "if", "in", "let", "match",
   "namespace", "open", "partial", "private", "protected", "return", "section", "show",
   "then", "else", "theorem", "def", "structure", "class", "instance", "where", "with",
   "import", "deriving", "variable", "universe", "axiom", "example", "abbrev", "inductive",
   "mutual", "opaque", "unsafe", "noncomputable", "macro", "syntax", "elab", "notation",
   "set_option", "attribute", "local", "scoped", "calc", "try", "catch", "finally", "mut",
   "unless", "repeat", "while", "break", "continue", "extends", "type", "Type", "Sort", "Prop",
   "fun", "λ", "forall", "exists", "sorry", "termination_by", "decreasing_by", "omit", "include"]

/-- A column name as a structure field: keywords are guillemet-quoted. -/
def fieldName (s : String) : String :=
  if leanKeywords.contains s then s!"«{s}»" else s

private def capitalize (s : String) : String :=
  match s.toList with
  | [] => ""
  | c :: rest => String.ofList (c.toUpper :: rest)

/-- A table name as a type name: `kernel_ins` → `KernelIns`. -/
def typeIdent (table : String) : String :=
  let cleaned := table.foldl (fun acc c =>
    acc.push (if c.isAlpha || c.isDigit then c else '_')) ""
  let segs := (cleaned.splitOn "_").filter (!·.isEmpty)
  let joined := segs.foldl (fun acc seg => acc ++ capitalize seg) ""
  if joined.isEmpty then "Table" else joined

/-- The raw Lean type of a column as stored: what an old row *is*, before
    any validated newtype or closed world re-interprets it. -/
def rawType (c : ColumnSpec) : String :=
  let base := match c.sqlType with
    | .integer => "Int64"
    | .text => "String"
    | .real => "Float"
  if c.nullable then s!"Option {base}" else base

/-- A `Col` as Lean source. REAL values render exactly (`renderRealExact`,
    parenthesized: the literal may be negative) so a frozen `V<n>.schema`
    re-elaborates to the very same double — `toString`'s six decimals would
    phantom-diff the snapshot against `base.specs`. A non-finite REAL has
    no literal; `migrate freeze` validates the schema (and so refuses one)
    before rendering, so meeting one here is a caller bug: panic. -/
def colLit : Col → String
  | .int v => s!"LeanDb.Col.int {v}"
  | .text v => s!"LeanDb.Col.text {String.quote v}"
  | .real v =>
      match renderRealExact v with
      | .ok s => s!"LeanDb.Col.real ({s})"
      | .error msg => panic! msg
  | .null => "LeanDb.Col.null"

private def strArr (xs : Array String) : String :=
  "#[" ++ String.intercalate ", " (xs.toList.map String.quote) ++ "]"

private def opt (f : α → String) : Option α → String
  | some a => s!"some ({f a})"
  | none => "none"

def sqlTypeLit : SqlType → String
  | .integer => "LeanDb.SqlType.integer"
  | .text => "LeanDb.SqlType.text"
  | .real => "LeanDb.SqlType.real"

/-- A `ColumnSpec` as a Lean structure-instance literal, every field
    spelled so the snapshot reads as documentation. -/
def columnLit (c : ColumnSpec) : String :=
  let fields : List String :=
    [s!"name := {String.quote c.name}", s!"sqlType := {sqlTypeLit c.sqlType}",
     s!"nullable := {c.nullable}", s!"fkTable := {opt String.quote c.fkTable}"] ++
    (if c.enum.isSome then [s!"enum := {opt strArr c.enum}"] else []) ++
    (if c.enumSet.isSome then [s!"enumSet := {opt strArr c.enumSet}"] else []) ++
    (if c.dflt.isSome then [s!"dflt := {opt colLit c.dflt}"] else []) ++
    (if c.shape.isSome then [s!"shape := {opt String.quote c.shape}"] else []) ++
    (if c.group.isSome then [s!"group := {opt String.quote c.group}"] else []) ++
    (if c.cascade then ["cascade := true"] else [])
  "{ " ++ String.intercalate ", " fields ++ " }"

def collateLit : Collate → String
  | .binary => "LeanDb.Collate.binary"
  | .nocase => "LeanDb.Collate.nocase"

/-- An `IndexSpec` as a Lean structure-instance literal. The collation
    (LDB-14) is fingerprint material, so a snapshot that dropped it would
    phantom-diff against the declared index. -/
def indexLit (ix : IndexSpec) : String :=
  let fields : List String :=
    [s!"unique := {ix.unique}", s!"columns := {strArr ix.columns}"] ++
    (if ix.partialWhere.isSome then [s!"partialWhere := {opt String.quote ix.partialWhere}"] else []) ++
    (if ix.name.isSome then [s!"name := {opt String.quote ix.name}"] else []) ++
    (if ix.collate.isSome then [s!"collate := {opt collateLit ix.collate}"] else [])
  "{ " ++ String.intercalate ", " fields ++ " }"

/-- A `TableSpec` as Lean source, one column per line. Named fields, so a
    field added to `TableSpec` later does not break a frozen snapshot, and
    every part of the spec the fingerprint reads is written: the indexes
    and the declared invariant (LDB-16) as well as the columns. -/
def tableLit (indent : String) (t : TableSpec) : String :=
  let block (field : String) (items : List String) : String :=
    String.intercalate "\n" <|
      [s!"{indent}  {field} := #["] ++
      (if items.isEmpty then [] else [String.intercalate ",\n" (items.map (s!"{indent}    " ++ ·))]) ++
      [s!"{indent}  ]"]
  let parts : List String :=
    [s!"{indent}\{ name := {String.quote t.name}", block "columns" (t.columns.toList.map columnLit)] ++
    (if t.indexes.isEmpty then [] else [block "indexes" (t.indexes.toList.map indexLit)]) ++
    (match t.invariant with
      | some n => [s!"{indent}  invariant := some {String.quote n}"]
      | none => [])
  String.intercalate ",\n" parts ++ s!" }"

/-- `List TableSpec` as Lean source. -/
def specsLit (specs : List TableSpec) : String :=
  match specs with
  | [] => "[]"
  | _ => "[\n" ++ String.intercalate ",\n" (specs.map (tableLit "  ")) ++ "\n]"

end LeanDb.Render
