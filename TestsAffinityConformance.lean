import LeanDb

/-! R1: `Migration.affinityOf` — the affinity normalization behind
`matchesSnapshot` — is conformance-tested against the vendored SQLite
itself, not just the prose of sqlite.org/datatype3.html §3.1. For every
declared type under test (representative spellings, the decision-order
edges, and randomized spellings from a fixed-seed LCG) the probe creates
a real table with that type, inserts canonical values of every storage
class, and compares the `typeof` SQLite reports with what the predicted
affinity class implies. -/

namespace TestsAffinityConformance

open LeanDb

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw <| IO.userError s!"FAIL: {message}"

private def expectOk (r : Except DbError α) (context : String) : IO α :=
  match r with
  | .ok a => pure a
  | .error e => throw <| IO.userError s!"FAIL: {context}: {e}"

/-! ## The probe values

One canonical value per storage class: an integer, numeric-looking
text, a real, non-numeric text, and a blob. -/

inductive ProbeVal where
  | int | numText | real | otherText | blob
deriving Repr, Inhabited

def ProbeVal.literal : ProbeVal → String
  | .int => "123"
  | .numText => "'123'"
  | .real => "1.5"
  | .otherText => "'abc'"
  | .blob => "x'0011'"

/-- The storage class the literal enters with, before affinity coercion —
    what a column with no affinity (empty type, BLOB: §3.1 rule 3) keeps. -/
def ProbeVal.storage : ProbeVal → String
  | .int => "integer"
  | .numText => "text"
  | .real => "real"
  | .otherText => "text"
  | .blob => "blob"

def ProbeVal.canonical : Array ProbeVal := #[.int, .numText, .real, .otherText, .blob]

/-- §3.1.1: what `typeof` must report for each probe value stored under
    affinity `a`. TEXT converts every numeric to text; REAL floats
    integers; INTEGER and NUMERIC convert numeric-looking text (and
    integral reals) but keep non-numeric text; a column with no affinity
    stores as-is. INTEGER and NUMERIC are observably identical here —
    their split is asserted by the pure classification checks below. -/
def expectedTypeof (a : Affinity) (v : ProbeVal) : String :=
  match a, v with
  | _, .blob => "blob"
  | .text, _ => "text"
  | .blob, v => v.storage
  | .real, .otherText => "text"
  | .real, _ => "real"
  | .numeric, .otherText => "text"
  | .integer, .otherText => "text"
  | .integer, .real => "real"
  | .numeric, .real => "real"
  | _, _ => "integer"

/-! ## Pure classification -/

/-- The decision order itself, including the edges where SQLite's scan
    priority matters (`BLOBINT` is the source's own example: INTEGER wins
    over BLOB; `CHARBLOB`/`TEXTBLOB`/`BLOBCHAR` are TEXT; `BLOBREAL` and
    `REALBLOB` are BLOB). -/
private def testAffinityOfClassification : IO Unit := do
  let expect (ty : String) (a : Affinity) : IO Unit :=
    check (Migration.affinityOf ty == a)
      s!"affinityOf \"{ty}\" must be {repr a}, got {repr (Migration.affinityOf ty)}"
  for ty in ["BIGINT", "SMALLINT", "TINYINT", "INT", "INTEGER", "POINT",
             "TEXTINT", "BLOBINT", "bigint"] do
    expect ty .integer
  for ty in ["VARCHAR(50)", "CHARACTER", "CLOB", "TEXT",
             "CHARBLOB", "TEXTBLOB", "BLOBCHAR", "varchar(20)"] do
    expect ty .text
  for ty in ["", "BLOB", "BLOBREAL", "REALBLOB"] do
    expect ty .blob
  for ty in ["REAL", "FLOAT", "DOUBLE PRECISION", "DOUB", "float"] do
    expect ty .real
  for ty in ["DECIMAL(10,2)", "NUMBER", "NUMERIC", "BOOLEAN", "DATETIME"] do
    expect ty .numeric

/-! ## Randomized spellings

A fixed-seed LCG (as in the other property tests) flips the case of
every letter and sprinkles spaces — never inside a parenthesized size,
where a split `1 0,2` would not parse — so SQLite's own scan of the
resulting type string must agree with `affinityOf` whatever the
spelling. -/

private def lcg (s : Nat) : Nat := (s * 1664525 + 1013904223) % 2147483648

/-- A spelling of `base`: random case per letter, spaces sprinkled at
    random gaps — never inside a parenthesized size. Deterministic in
    the seed. -/
private def randomSpelling (seed : Nat) (base : String) : String × Nat :=
  Id.run do
    let mut s := seed
    let mut out := ""
    let mut depth := 0
    let mut lastSpace := false
    for c in base.toList do
      if c == '(' then depth := depth + 1
      if c == ')' then depth := depth - 1
      s := lcg s
      let putSpace := s % 4 == 0 && !out.isEmpty && depth == 0 && !lastSpace
      if putSpace then out := out ++ " "
      lastSpace := putSpace
      s := lcg s
      out := out.push (if c.isAlpha && s % 2 == 0 then c.toUpper else c.toLower)
    return (out, s)

/-- Spelling candidates may not isolate a token that is a SQL keyword:
    `SMALL IN T` does not parse (type-name tokens must be identifiers). -/
private def spellingKeyword (tok : String) : Bool :=
  ["in", "is", "as", "on", "or", "and", "not", "set", "end", "all", "by", "if"].contains tok.toLower

private def spellingBases : Array String :=
  #["BIGINT", "SMALLINT", "TINYINT", "VARCHAR(50)", "CHARACTER", "CLOB", "TEXT",
    "BLOB", "REAL", "FLOAT", "DOUBLE PRECISION", "DECIMAL(10,2)", "NUMBER",
    "NUMERIC", "BOOLEAN"]

private def randomSpellings (n : Nat) (seed : Nat) : Array String := Id.run do
  let mut s := seed
  let mut out := #[]
  while out.size < n do
    s := lcg s
    let base := spellingBases[s % spellingBases.size]!
    let (sp, s') := randomSpelling s base
    s := s'
    if (sp.splitOn " ").all (!spellingKeyword ·) then
      out := out.push sp
  return out

/-! ## The differential probe -/

structure ProbeHost where
  note : String := ""
  deriving Repr, LeanDb.Entity

private def specs : List TableSpec := [Entity.spec ProbeHost]

private def probePath : System.FilePath := ".lake" / "leandb_test_affinity_conformance.sqlite"

private def fresh (p : System.FilePath) : IO Unit := do
  if ← p.pathExists then IO.FS.removeFile p
  for suffix in ["-wal", "-shm"] do
    let side : System.FilePath := p.toString ++ suffix
    if ← side.pathExists then IO.FS.removeFile side

/-- The probe table's value column: an empty declared type is a column
    with no type at all (the §3.1 rule-3 BLOB affinity). -/
private def probeDdl (declared : String) : String :=
  if declared.isEmpty then "CREATE TABLE \"probe\" (v)"
  else s!"CREATE TABLE \"probe\" (v {declared})"

/-- Create the probe table with the declared type, insert each canonical
    value, and read `typeof(v)` back per row — the vendored SQLite's own
    coercion, seen through `untrackedSqlite`. -/
private def probe (db : SQLite) (declared : String) : IO (Array String) := do
  db.exec "DROP TABLE IF EXISTS \"probe\""
  db.exec (probeDdl declared)
  for v in ProbeVal.canonical do
    db.exec s!"INSERT INTO \"probe\" (v) VALUES ({v.literal})"
  let st ← db.prepare "SELECT typeof(v) FROM \"probe\" ORDER BY rowid"
  let mut out := #[]
  repeat
    if ← st.step then
      out := out.push (← st.columnText 0)
    else break
  return out

private def runProbe (db : SQLite) (declared : String) (kind : String) : IO Unit := do
  let aff := Migration.affinityOf declared
  let got ← probe db declared
  check (got.size == ProbeVal.canonical.size)
    s!"probe \"{declared}\": read {got.size} typeof rows, expected {ProbeVal.canonical.size}"
  for i in [0:ProbeVal.canonical.size] do
    let v := ProbeVal.canonical[i]!
    let want := expectedTypeof aff v
    check (got[i]? == some want)
      s!"SQLite contradicts affinityOf: declared \"{declared}\" ({kind}, {repr aff}) \
         value {v.literal}: predicted {want}, SQLite reports {got[i]?}"

private def testAffinityConformance : IO Unit := do
  fresh probePath
  let representative : List String :=
    ["BIGINT", "SMALLINT", "TINYINT", "INT", "INTEGER", "POINT",
     "VARCHAR(50)", "CHARACTER", "CLOB", "TEXT",
     "", "BLOB",
     "REAL", "FLOAT", "DOUBLE PRECISION",
     "DECIMAL(10,2)", "NUMBER", "NUMERIC",
     -- decision-order edges: what the prose must match SQLite on
     "BLOBINT", "TEXTINT", "CHARBLOB", "TEXTBLOB", "BLOBCHAR", "BLOBREAL", "REALBLOB"]
  discard <| expectOk (← withDb probePath specs do
    untrackedSqlite fun db => do
      for ty in representative do
        runProbe db ty "representative/edge"
      for ty in randomSpellings 40 42 do
        runProbe db ty "randomized"
      return ()) "affinity conformance probe"

def run : IO Unit := do
  testAffinityOfClassification
  testAffinityConformance

end TestsAffinityConformance
