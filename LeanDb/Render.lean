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
    before rendering, so meeting one here is a caller bug: panic. INTs
    render via `Int64.ofNat` (negated for negatives): Lean parses a bare
    `f -5` as binary subtraction, not application, and even parenthesized
    a negative literal's magnitude (`Int64.minValue`) is outside Int64
    literal range — `ofNat` reduces mod 2^64 to the exact value either
    way, mirroring the derive's own syntax-level emitter. -/
def colLit : Col → String
  | .int v =>
      let n : Nat := v.toInt.natAbs
      if v.toInt < 0 then s!"LeanDb.Col.int (-(Int64.ofNat {n}))"
      else s!"LeanDb.Col.int (Int64.ofNat {n})"
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

/-- A `TableSpec` as Lean source, one column per line. -/
def tableLit (indent : String) (t : TableSpec) : String :=
  let cols := t.columns.toList.map fun c => s!"{indent}    {columnLit c}"
  String.intercalate "\n" <|
    [s!"{indent}⟨{String.quote t.name}, #["] ++
    (match cols with
      | [] => []
      | _ => [String.intercalate ",\n" cols]) ++
    [s!"{indent}  ]⟩"]

/-- `List TableSpec` as Lean source. -/
def specsLit (specs : List TableSpec) : String :=
  match specs with
  | [] => "[]"
  | _ => "[\n" ++ String.intercalate ",\n" (specs.map (tableLit "  ")) ++ "\n]"

end LeanDb.Render
