import LeanDb
import FixturePortable

/-! LDB-12: `DbJson.via` — JSON codecs for nested types with proof fields.

`ProofText` (two proof fields over its data field `s`) cannot be derived —
a derive cannot walk a field whose type depends on an earlier field. The
native package stores it through its data representation (`String` here)
with `DbJson.via`, derives the parents post-hoc (the LDB-10 pattern), and
the schema, the fingerprint and the decode errors all see the data shape.
`ProofTextWide` is the same tree over a wider data representation: changing
the data field's type moves the fingerprint. -/

namespace TestsLdb12

open LeanDb

/-- The native-package pattern: store `s`, re-decide the proofs on decode. -/
instance : LeanDb.DbJson ProofText :=
  LeanDb.DbJson.via (·.s) ProofText.make

instance : LeanDb.DbJson ProofTextWide :=
  LeanDb.DbJson.via (fun t => (t.s, t.lang)) (fun d => ProofTextWide.make d.1 d.2)

-- the parent derives resolve the `via` instances' `JsonShape` (the data shape)
deriving instance LeanDb.DbJson for ProofRun, ProofParagraph, ProofDoc, ProofWideDoc

instance : ColCodec ProofText := ColCodec.json ProofText
instance : ColCodec ProofTextWide := ColCodec.json ProofTextWide
instance : ColCodec ProofRun := ColCodec.json ProofRun
instance : ColCodec ProofParagraph := ColCodec.json ProofParagraph
instance : ColCodec ProofDoc := ColCodec.json ProofDoc
instance : ColCodec ProofWideDoc := ColCodec.json ProofWideDoc

/-- The derived record: the two-proof-field structure sits three levels
    down (`doc` → `paras` → `runs` → `text`), plus a nullable one. -/
structure ProofPage where
  doc : ProofDoc
  note : Option ProofText
  deriving LeanDb.Entity

structure ProofWidePage where
  doc : ProofWideDoc
  deriving LeanDb.Entity

end TestsLdb12

/--
error: deriving LeanDb.DbJson: field 'normal' of GuardedJson depends on another field; dependent fields are not stored — declare `instance : LeanDb.DbJson … := LeanDb.DbJson.via encode parse` for the field's type over its data representation
-/
#guard_msgs (error) in
structure GuardedJson where
  a : Nat
  normal : a = a
  deriving LeanDb.DbJson

/--
error: deriving LeanDb.Entity: field 'normal' of GuardedEntity depends on an earlier field; proof/dependent fields are not stored — persist the data representation instead and re-decide the proofs on decode with `LeanDb.DbJson.via`
-/
#guard_msgs (error) in
structure GuardedEntity where
  a : Nat
  normal : a = a
  deriving LeanDb.Entity

namespace TestsLdb12

open LeanDb

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw <| IO.userError s!"FAIL: {message}"

private def check' (condition : Bool) (message : String) : DbM Unit :=
  unless condition do throw (.sqlite s!"FAIL: {message}")

private def expectOk (r : Except DbError α) (context : String) : IO α :=
  match r with
  | .ok a => pure a
  | .error e => throw <| IO.userError s!"FAIL: {context}: {e}"

/-- Fixture values must satisfy the proofs, so `make` failures are test bugs. -/
private def mkT (s : String) : IO ProofText :=
  match ProofText.make s with
  | .ok t => pure t
  | .error e => throw <| IO.userError s!"FAIL: bad fixture text {String.quote s}: {e}"

private def pj (s : String) : IO Lean.Json :=
  match Lean.Json.parse s with
  | .ok j => pure j
  | .error e => throw <| IO.userError s!"FAIL: bad test JSON: {e}"

private def dbPath : System.FilePath := ".lake" / "leandb_test_ldb12.sqlite"

private def fresh : IO Unit := do
  if ← dbPath.pathExists then IO.FS.removeFile dbPath
  for suffix in ["-wal", "-shm"] do
    let side : System.FilePath := dbPath.toString ++ suffix
    if ← side.pathExists then IO.FS.removeFile side

/-- `via` encodes the data representation, re-decides the proofs on decode,
    and its shape is `σ`'s — which is what the parent derive resolves. -/
private def testViaCodecs : IO Unit := do
  let t ← mkT "hello"
  check ((Lean.toJson t).compress == "\"hello\"") "via encodes the data representation"
  check ((Lean.fromJson? (Lean.toJson t) : Except String ProofText).toOption.map (·.s) == some "hello")
    "via round trip"
  -- a stored value that fails `parse` carries the validator's message
  match (Lean.fromJson? (Lean.toJson "") : Except String ProofText) with
  | .error m => check ((m.splitOn "text: empty").length > 1) s!"parse message, got {m}"
  | .ok _ => throw <| IO.userError "FAIL: empty text accepted"
  match (Lean.fromJson? (Lean.toJson "a\nb") : Except String ProofText) with
  | .error _ => pure ()
  | .ok _ => throw <| IO.userError "FAIL: text with a line break accepted"
  -- the shape the fingerprint and `migrate` see is `σ`'s, not an opaque blob
  check (JsonShape.shape ProofText == "String") s!"via shape is the data shape, got {JsonShape.shape ProofText}"
  check (JsonShape.shape (Option ProofText) == "String?") "Option lifts the data shape"
  check (JsonShape.shape ProofRun == "ProofRun{text:String,bold:Bool=}")
    s!"parent derive sees the data shape, got {JsonShape.shape ProofRun}"
  check (JsonShape.shape ProofDoc ==
      "ProofDoc{title:String,paras:[ProofParagraph{runs:[ProofRun{text:String,bold:Bool=}]}]=}")
    s!"three levels down, got {JsonShape.shape ProofDoc}"
  check (JsonShape.shape ProofWideDoc ==
      "ProofWideDoc{title:(String,String),paras:[ProofParagraph{runs:[ProofRun{text:String,bold:Bool=}]}]=}")
    s!"the wider data representation, got {JsonShape.shape ProofWideDoc}"

/-- The column's spec and the fingerprint see the data shape; changing the
    data field's type moves the fingerprint. -/
private def testViaSchema : IO Unit := do
  let cols := Entity.columns ProofPage
  check (cols.map (·.name) == #["doc", "note"]) "column names"
  check ((cols.getD 1 default).shape == some (JsonShape.shape ProofText))
    "the nullable column lifts the data shape"
  check ((cols.getD 1 default).nullable) "the Option JSON column is nullable"
  check ((cols.getD 0 default).shape == some (JsonShape.shape ProofDoc))
    "the column's shape is the parent derive's shape"
  -- `schema` JSON shows the data shape, not an opaque blob
  let schemaJsonStr := (Entity.spec ProofPage).toJson.compress
  check ((schemaJsonStr.splitOn "\"shape\":\"ProofDoc{title:String,").length == 2)
    s!"schema shows the data shape, got {schemaJsonStr}"
  -- changing the data field's type changes the fingerprint
  check (JsonShape.shape ProofDoc != JsonShape.shape ProofWideDoc) "the two data representations differ"
  check (fingerprint [Entity.spec ProofPage] != fingerprint [Entity.spec ProofWidePage])
    "changing the data field's type changes the fingerprint"
  -- and the schema still round-trips through the stored schema JSON
  check ((specsFromJson? (specsToJson [Entity.spec ProofPage, Entity.spec ProofWidePage])).toOption ==
      some [Entity.spec ProofPage, Entity.spec ProofWidePage]) "schema JSON round trip"

/-- Insert/select round-trips through a real instance. -/
private def testViaRoundTrip : IO Unit := do
  fresh
  let title ← mkT "title"
  let body ← mkT "body"
  let note ← mkT "note"
  let doc : ProofDoc := { title, paras := [{ runs := [{ text := body, bold := true }] }] }
  let r ← withDb dbPath [Entity.spec ProofPage] do
    discard <| insert ProofPage { doc, note := some note }
    let rows ← fetchAll ProofPage
    check' (rows.size == 1) "one row"
    match rows[0]? with
    | none => check' false "row present"
    | some back =>
      let back := back.val
      let run? : Option ProofRun := back.doc.paras[0]?.bind (·.runs[0]?)
      check' (back.doc.title.s == "title" && back.note.map (·.s) == some "note") "scalars round trip"
      check' (run?.map (·.text.s) == some "body" && run?.map (·.bold) == some true)
        "the nested proof-field structure round-trips three levels down"
  discard <| expectOk r "insert/select round trip"

/-- A stored JSON value that fails `parse` is a `DbError.decode` naming the
    table and field, with the `parse` message appended. -/
private def testViaDecodeErrors : IO Unit := do
  -- pure decode: the column value parses as the data representation but fails the validator
  match (Entity.decode #[.text "{\"title\":\"\"}", .null] : Except DbError ProofPage) with
  | .error (.decode "proof_page" "doc" m) =>
      check ((m.splitOn "text: empty").length > 1) s!"parse message appended, got {m}"
  | .error e => throw <| IO.userError s!"FAIL: wrong error for a failing parse: {e}"
  | .ok _ => throw <| IO.userError "FAIL: a value that fails parse decoded"
  -- the JSON boundary: same typed error, table and field named
  -- row JSON spells a JSON column as a JSON string of compressed JSON
  let badDoc := Lean.Json.mkObj [("doc", Lean.Json.str (Lean.Json.mkObj [("title", Lean.Json.str "")]).compress)]
  match rowOfJson ProofPage badDoc with
  | .error (.decode "proof_page" "doc" m) =>
      check ((m.splitOn "text: empty").length > 1) s!"parse message appended, got {m}"
  | .error e => throw <| IO.userError s!"FAIL: wrong error via row JSON: {e}"
  | .ok _ => throw <| IO.userError "FAIL: a row JSON whose doc fails parse was accepted"
  -- the real instance: a corrupt stored row is a storage error, not a client error
  fresh
  let title ← mkT "t"
  let body ← mkT "b"
  let doc : ProofDoc := { title, paras := [{ runs := [{ text := body }] }] }
  discard <| expectOk (← withDb dbPath [Entity.spec ProofPage] do
    discard <| insert ProofPage { doc, note := none }) "insert"
  (← SQLite.open dbPath).exec "UPDATE proof_page SET note = '\"\"' WHERE id = 1"
  match ← withDb dbPath [Entity.spec ProofPage] (fetchAll ProofPage) with
  | .error (.decode "proof_page" "note" m) =>
      check ((m.splitOn "text: empty").length > 1) s!"parse message appended, got {m}"
  | .error e => throw <| IO.userError s!"FAIL: corrupt stored JSON: wrong error {e}"
  | .ok _ => throw <| IO.userError "FAIL: a stored value that fails parse was read back"

def run : IO Unit := do
  testViaCodecs
  testViaSchema
  testViaRoundTrip
  testViaDecodeErrors

end TestsLdb12
