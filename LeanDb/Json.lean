import Lean.Data.Json
import LeanDb.Entity

namespace LeanDb

/-! # JSON, derived from the schema

Everything here is computed from `Entity`/`TableSpec` — the JSON surface
cannot drift from the types. Incoming JSON decodes *through* the column
codecs and smart constructors: a caller can be wrong, never ill-typed.
-/

open Lean (Json ToJson toJson)

def Col.toJson : Col → Json
  | .int v => Lean.toJson v.toInt
  | .text v => Json.str v
  | .real v => Lean.toJson v
  | .null => Json.null

/-- A column value as row JSON: an `EnumSet` column's bitmask renders as
    the array of its members' names (`["silu","gelu"]`, declaration
    order); everything else as `Col.toJson`. -/
def Col.toJsonFor (spec : ColumnSpec) : Col → Json
  | .int v =>
      match spec.enumSet with
      | some vs =>
          let bits := v.toNatClampNeg.toUInt64
          Json.arr <| vs.zipIdx.filterMap fun (name, k) =>
            if (bits >>> k.toUInt64) &&& 1 != 0 then some (Json.str name) else none
      | none => Col.toJson (.int v)
  | c => c.toJson

/-- Decode one JSON value as the column's SQL type. An `EnumSet` column
    takes an array of variant names (an unknown name is refused by name)
    or, for round-tripping, the bare bitmask. -/
def Col.fromJson (spec : ColumnSpec) (j : Json) : Except String Col :=
  match j with
  | Json.null =>
      if spec.nullable then .ok .null
      else .error s!"{spec.name}: null not allowed"
  | Json.bool b =>
      -- only an actual Bool codec accepts JSON booleans; a Nat/Int64
      -- INTEGER must not silently coerce true/false to 1/0
      if spec.boolCodec && spec.sqlType == .integer && spec.enumSet.isNone then
        .ok (.int (if b then 1 else 0))
      else .error s!"{spec.name}: boolean not allowed for a {spec.sqlType.render} column"
  | Json.arr items =>
      match spec.enumSet with
      | some vs => do
          let mut bits : UInt64 := 0
          for item in items do
            let name ← item.getStr?
            match vs.findIdx? (· == name) with
            | some k => bits := bits ||| ((1 : UInt64) <<< k.toUInt64)
            | none => throw s!"{spec.name}: {String.quote name} is not in the closed world {vs}"
          return .int (Int64.ofNat bits.toNat)
      | none => .error s!"{spec.name}: array not allowed for a {spec.sqlType.render} column"
  | _ =>
      match spec.sqlType with
      | .integer => do
          let i ← j.getInt?
          if i < Int64.minValue.toInt || i > Int64.maxValue.toInt then
            throw s!"{spec.name}: {i} out of INTEGER range"
          return .int (Int64.ofInt i)
      | .text => .text <$> j.getStr?
      | .real => do
          let v ← (j.getNum? <&> (·.toFloat))
          -- as at the bind boundary (`Db.bindCol`): a NaN would store as
          -- NULL and an infinity would leave every JSON surface a string
          if v.isNaN || v.isInf then
            throw s!"{spec.name}: REAL value is non-finite ({if v.isNaN then "NaN" else "infinite"})"
          return .real v

/-- A nested value type that lives in one JSON TEXT column: its JSON
    encoding both ways plus its declared shape. Instances come from
    `deriving LeanDb.DbJson` (see `LeanDb.Derive`) or from `DbJson.via`,
    and — unlike Lean's own derive — an omitted field with a structure
    default takes the default, so an additive change to a nested type
    still decodes old rows. (Named `DbJson`, not `Json`: a `LeanDb.Json`
    would shadow `Lean.Json` in every engine module that opens it.) -/
class DbJson (α : Type) extends ToJson α, Lean.FromJson α, JsonShape α

/-- A `DbJson` codec for `α` through a data representation `σ` that has
    one — how a type with proof fields (whose Lean type depends on an
    earlier field, so a derive cannot walk it) is stored after all:
    `encode` erases the proofs, `parse` re-decides them, and the JSON —
    and therefore the `JsonShape` the fingerprint and `migrate` see — is
    `σ`'s, never an opaque blob. Declared as
    `instance : DbJson Text := DbJson.via encode parse`; because `DbJson`
    extends `JsonShape`, the instance also registers `JsonShape α`, so a
    parent `deriving LeanDb.DbJson` resolves the field as `σ`'s data
    shape. A stored value that fails `parse` decodes as the typed
    `DbError.decode table field` with the `parse` message, the same way a
    `ColCodec.via` scalar's validator fails. -/
@[reducible] def DbJson.via [Lean.ToJson σ] [Lean.FromJson σ] [JsonShape σ]
    (encode : α → σ) (parse : σ → Except String α) : DbJson α where
  toJson a := Lean.toJson (encode a)
  fromJson? j := (Lean.fromJson? (α := σ) j) >>= parse
  shape := JsonShape.shape σ

/-- The codec of a JSON column: compressed JSON in a TEXT column, decoded
    through `validate` (a smart constructor over the whole value, so a
    row written by an older build or by the CLI is refused the same way a
    Lean constructor call would be). The column's `shape` is the type's
    `JsonShape`; `columnSpec` reads it off the codec. -/
@[reducible] def ColCodec.json (α : Type) [ToJson α] [Lean.FromJson α] [JsonShape α]
    (validate : α → Except String α := .ok) : ColCodec α where
  sqlType := .text
  toCol a := .text (toJson a).compress
  fromCol
    | .text t => Json.parse t >>= Lean.fromJson? >>= validate
    | c => .error s!"expected TEXT, found {c.describe}"
  shape := some (JsonShape.shape α)

/-- `fromJson?` of `key` in `json`, or `dflt ()` when the key is absent —
    how a `deriving LeanDb.DbJson` decoder treats a field with a default.
    An explicit `null` is a present value, decoded as such. -/
def jsonFieldOr [Lean.FromJson α] (json : Json) (key : String) (dflt : Unit → α) :
    Except String α :=
  match json.getObjVal? key with
  | .ok v => Lean.fromJson? v
  | .error _ => .ok (dflt ())

def DbError.toJson (e : DbError) : Json :=
  Json.mkObj [("ok", Json.bool false), ("code", Json.str e.code),
    ("message", Json.str e.message)]

def ColumnSpec.toJson (c : ColumnSpec) : Json :=
  Json.mkObj <|
    [("name", Json.str c.name), ("type", Json.str c.sqlType.render),
     ("nullable", Json.bool c.nullable)]
    ++ (c.fkTable.map fun fk => ("references", Json.str fk)).toList
    ++ (c.enum.map fun vs => ("enum", Json.arr (vs.map Json.str))).toList
    ++ (c.enumSet.map fun vs => ("enumSet", Json.arr (vs.map Json.str))).toList
    ++ (c.dflt.map fun v => ("default", v.toJson)).toList
    ++ (c.shape.map fun s => ("shape", Json.str s)).toList
    ++ (c.group.map fun g => ("group", Json.str g)).toList
    ++ (if c.cascade then [("cascade", Json.bool true)] else [])

def IndexSpec.toJson (ix : IndexSpec) : Json :=
  Json.mkObj <|
    [("unique", Json.bool ix.unique),
     ("columns", Json.arr (ix.columns.map Json.str))]
    ++ (ix.partialWhere.map fun w => ("where", Json.str w)).toList
    ++ (ix.name.map fun n => ("name", Json.str n)).toList
    ++ (ix.collate.map fun k => ("collate", Json.str k.toSql)).toList

def IndexSpec.fromJson? (j : Json) : Except String IndexSpec := do
  let unique ← match j.getObjVal? "unique" with
    | .ok v => v.getBool?
    | .error _ => pure false
  let cols ← (← j.getObjVal? "columns" >>= (·.getArr?)).mapM (·.getStr?)
  let partialWhere ← match j.getObjVal? "where" with
    | .ok v => some <$> v.getStr?
    | .error _ => pure none
  let name ← match j.getObjVal? "name" with
    | .ok v => some <$> v.getStr?
    | .error _ => pure none
  let collate ← match j.getObjVal? "collate" with
    | .ok v => do
        let s ← v.getStr?
        match s with
        | "BINARY" => pure (some .binary)
        | "NOCASE" => pure (some .nocase)
        | _ => .error s!"unknown index collation {String.quote s}"
    | .error _ => pure none
  return { unique, columns := cols, partialWhere, name, collate }

def TableSpec.toJson (t : TableSpec) : Json :=
  Json.mkObj <|
    [("name", Json.str t.name),
     ("columns", Json.arr (t.columns.map (·.toJson)))]
    ++ (if t.indexes.isEmpty then [] else
      [("indexes", Json.arr (t.indexes.map (·.toJson)))])
    ++ (match t.invariant with
      | some n => [("invariant", Json.str n)]
      | none => [])

def SqlType.fromJson? (j : Json) : Except String SqlType := do
  match ← j.getStr? with
  | "INTEGER" => return .integer
  | "TEXT" => return .text
  | "REAL" => return .real
  | s => throw s!"unknown SQL type {s}"

def ColumnSpec.fromJson? (j : Json) : Except String ColumnSpec := do
  let name ← j.getObjVal? "name" >>= (·.getStr?)
  let sqlType ← SqlType.fromJson? (← j.getObjVal? "type")
  let nullable ← j.getObjVal? "nullable" >>= (·.getBool?)
  -- every optional field decodes STRICTLY: a present-but-malformed value
  -- is an error, not an absence. The stored `schema_json` is diffed
  -- against the code's specs by `migrate`, so a lossy decode (silently
  -- dropping a malformed field) would make the instance "remember" a
  -- schema that was never stored — the phantom diff the round-trip rule
  -- below forbids. Only the KEY's absence means absent.
  let optStr (key : String) : Except String (Option String) :=
    match j.getObjVal? key with
    | .ok v => some <$> (v.getStr? |>.mapError fun m => s!"{name}: malformed \"{key}\": {m}")
    | .error _ => pure none
  let optStrArr (key : String) : Except String (Option (Array String)) :=
    match j.getObjVal? key with
    | .ok v => do
        let a ← v.getArr? |>.mapError fun m => s!"{name}: malformed \"{key}\": {m}"
        let mut vs : Array String := #[]
        for x in a do
          match x.getStr? with
          | .ok str => vs := vs.push str
          | .error _ => throw s!"{name}: \"{key}\" must be an array of strings"
        pure (some vs)
    | .error _ => pure none
  let fkTable ← optStr "references"
  let enum ← optStrArr "enum"
  let enumSet ← optStrArr "enumSet"
  let partial_ : ColumnSpec :=
    { name := name, sqlType := sqlType, nullable := nullable,
      fkTable := fkTable, enum := enum, enumSet := enumSet }
  -- default roundtrips through the column's own type (stored schema JSON
  -- must decode identically or migrations would see phantom diffs)
  let dflt ← match j.getObjVal? "default" with
    | .ok v => some <$> (Col.fromJson partial_ v |>.mapError fun m => s!"{name}: malformed \"default\": {m}")
    | .error _ => pure none
  let shape ← optStr "shape"
  let group ← optStr "group"
  let cascade ← match j.getObjVal? "cascade" with
    | .ok v => (v.getBool? |>.mapError fun m => s!"{name}: malformed \"cascade\": {m}")
    | .error _ => pure false
  return { partial_ with dflt, shape, group, cascade }

def TableSpec.fromJson? (j : Json) : Except String TableSpec := do
  let name ← j.getObjVal? "name" >>= (·.getStr?)
  let cols ← j.getObjVal? "columns" >>= (·.getArr?)
  let indexes ← match j.getObjVal? "indexes" with
    | .ok v => (← v.getArr?).mapM IndexSpec.fromJson?
    | .error _ => pure #[]
  let invariant ← match j.getObjVal? "invariant" with
    | .ok v => some <$> (v.getStr? |>.mapError fun m => s!"{name}: malformed \"invariant\": {m}")
    | .error _ => pure none
  return { name, columns := ← cols.mapM ColumnSpec.fromJson?, indexes, invariant }

/-- Serialize/parse a whole schema — how an instance remembers the shape
    it was last migrated to. -/
def specsToJson (specs : List TableSpec) : Json :=
  Json.arr (specs.toArray.map (·.toJson))

def specsFromJson? (j : Json) : Except String (List TableSpec) := do
  return (← (← j.getArr?).mapM TableSpec.fromJson?).toList

/-- The schema surface: derived from the specs, which are derived from the
    types. There is no other source. -/
def schemaJson (name : String) (specs : List TableSpec) : Json :=
  Json.mkObj [("ok", Json.bool true), ("base", Json.str name),
    ("fingerprint", Json.str (fingerprint specs)),
    ("tables", Json.arr (specs.toArray.map (·.toJson)))]

/-- The key of a flattened column inside its group's JSON object: the
    column name without the `<group>_` prefix (`launch_smemBytes` →
    `smemBytes`). The column name itself for an ungrouped column. -/
def ColumnSpec.subKey (c : ColumnSpec) : String :=
  match c.group with
  | some g => (c.name.drop (g.length + 1)).toString
  | none => c.name

/-- A child list as row JSON (LEP-0003 D): an array of record objects in
    list order, position implicit. -/
def childListJson [Entity α] (link : ChildLink α) (a : α) : Json :=
  let cols := link.recordColumns
  Json.arr <| (link.rows a).map fun row =>
    Json.mkObj ((cols.zip row).toList.map fun (c, v) => (c.name, v.toJsonFor c))

/-- A stored row as JSON: id plus one field per column, by column name.
    The columns of a flattened inline field (LEP-0003 C, `group`) nest as
    one object under the field name: `"launch": {"block": …, …}`; a child
    list (LEP-0003 D) is an array of record objects: `"ins": [{…}, …]`. -/
def rowJson (α : Type) [Entity α] (s : Stored α) : Json :=
  let fields := (Entity.columns α).zip (Entity.encode s.val)
  let (flat, groups) := fields.foldl (init := ((#[] : Array (String × Json)), (#[] : Array (String × Array (String × Json)))))
    fun (flat, groups) (c, v) =>
      match c.group with
      | none => (flat.push (c.name, v.toJsonFor c), groups)
      | some g =>
          match groups.findIdx? (·.1 == g) with
          | some i => (flat, groups.modify i fun (g, kvs) => (g, kvs.push (c.subKey, v.toJsonFor c)))
          | none => (flat, groups.push (g, #[(c.subKey, v.toJsonFor c)]))
  Json.mkObj <| ("id", Lean.toJson s.id.toInt64.toInt) :: flat.toList
    ++ groups.toList.map (fun (g, kvs) => (g, Json.mkObj kvs.toList))
    ++ (Entity.children (α := α)).map fun link => (link.field, childListJson link s.val)

/-- The columns of `α` with whether each is derived, in declaration order. -/
private def columnsWithDerived (α : Type) [Entity α] : Array (ColumnSpec × Bool) :=
  (Entity.fields (α := α)).map fun f => (Entity.fieldSpec f, Entity.isDerived f)

/-- Refuse a row object whose keys name no column. At the top level a key
    is a column name or a group (inline field) name; a group key must hold
    an object whose keys are that group's sub-keys. -/
private def checkRowKeys (α : Type) [Entity α] (table : String) (j : Json) :
    Except DbError Unit := do
  let obj ← match j with
    | .obj obj => .ok obj
    | _ => .error (.decode table "*" "expected a JSON object")
  let cols := Entity.columns α
  let known := cols.map (·.name)
  let groups := (cols.filterMap (·.group)).toList.eraseDups
  let links := Entity.children (α := α)
  for (name, v) in obj.toList do
    if let some link := links.find? (·.field == name) then
      -- a child list: an array of record objects, each over the record's columns
      let items ← match v with
        | .arr items => .ok items
        | _ => .error (.decode table name s!"expected an array of {String.quote name} records")
      let recordKeys := link.recordColumns.map (·.name)
      for item in items do
        let sub ← match item with
          | .obj sub => .ok sub
          | _ => .error (.decode link.table "*" s!"expected an object with the fields of a {String.quote name} record")
        for (k, _) in sub.toList do
          unless recordKeys.contains k do
            throw (.decode link.table k s!"unknown field; fields of {name}: {recordKeys.toList}")
    else if groups.contains name then
      let sub ← match v with
        | .obj sub => .ok sub
        | _ => .error (.decode table name
            s!"expected an object with the fields of {String.quote name} (or use the flat {name}_<field> keys)")
      let subKeys := cols.filterMap fun c => if c.group == some name then some c.subKey else none
      for (k, _) in sub.toList do
        unless subKeys.contains k do
          throw (.decode table s!"{name}_{k}" s!"unknown field; fields of {name}: {subKeys.toList}")
    else
      unless known.contains name do
        throw (.decode table name s!"unknown field; fields: {known.toList}")

/-- Where an incoming row object supplies column `c`: under its flat key
    (`"launch_smemBytes"`) or, for a flattened column, inside its group's
    object (`"launch": {"smemBytes": …}`). Both at once is refused by name. -/
private def rowValue? (table : String) (j : Json) (c : ColumnSpec) : Except DbError (Option Json) := do
  let flat := (j.getObjVal? c.name).toOption
  match c.group with
  | none => return flat
  | some g =>
      let nested := (j.getObjVal? g).toOption.bind fun o => (o.getObjVal? c.subKey).toOption
      match flat, nested with
      | some _, some _ =>
          throw (.decode table c.name
            s!"given twice: as {String.quote c.name} and as {String.quote c.subKey} inside {String.quote g}")
      | some v, none | none, some v => return some v
      | none, none => return none

/-- One record of a child list from its JSON object: the record's columns
    with the same omission rules as a row (`rowOfJson`), errors naming the
    child table and column. -/
def childRecordOfJson [Entity α] (link : ChildLink α) (j : Json) : Except DbError (Array Col) :=
  link.recordColumns.mapM fun c => do
    match j.getObjVal? c.name with
    | .ok v =>
        match Col.fromJson c v with
        | .ok col => .ok col
        | .error m => .error (.decode link.table c.name m)
    | .error _ =>
        match c.dflt with
        | some col => .ok col
        | none =>
            if c.nullable then .ok .null
            else .error (.decode link.table c.name "missing required field")

/-- A child list from its JSON array, positions by order. -/
def childRowsOfJson [Entity α] (link : ChildLink α) (j : Json) :
    Except DbError (Array (Nat × Array Col)) := do
  let items ← match j with
    | .arr items => .ok items
    | _ => .error (.decode (Entity.tableName α) link.field s!"expected an array of {String.quote link.field} records")
  items.zipIdx.mapM fun (item, i) => do return (i, ← childRecordOfJson link item)

/-- Decode a full row from JSON field-by-field, then through the entity's
    codecs (and thus every smart constructor). An omitted field takes its
    declared default; without one it is `null` if the column is nullable
    and a typed error otherwise. An explicit JSON `null` is always `null`,
    default or not. A derived column is recomputed from its sources: it
    may be omitted, and a supplied value is ignored. A flattened inline
    field may come nested (`"launch": {…}`) or flat (`"launch_block"`). A
    child list (LEP-0003 D) is an array of record objects under the field
    name, position implicit; omitted, it is empty. -/
def rowOfJson (α : Type) [Entity α] (j : Json) : Except DbError α := do
  let table := Entity.tableName α
  checkRowKeys α table j
  let cols ← (columnsWithDerived α).mapM fun (c, derived) => do
    if derived then return .null
    match ← rowValue? table j c with
    | some v =>
        match Col.fromJson c v with
        | .ok col => .ok col
        | .error m => .error (.decode table c.name m)
    | none =>
        match c.dflt with
        | some col => .ok col
        | none =>
            if c.nullable then .ok .null
            else .error (.decode table c.name "missing required field")
  let a ← Entity.decodeRecomputing cols
  -- child lists (LEP-0003 D): an omitted list is empty
  (Entity.children (α := α)).foldlM (init := a) fun a link => do
    let rows ← match j.getObjVal? link.field with
      | .ok v => childRowsOfJson link v
      | .error _ => pure #[]
    link.attachRecomputing rows a

/-- Overlay a partial JSON object onto an existing row at the column level,
    then re-decode — validation applies to the merged result. This is the
    CLI's `update <table> <id> <partial-json>`. Derived columns are
    recomputed from the merged sources, never kept from the old row. A
    nested group object overlays only the sub-fields it names; a child
    list (LEP-0003 D) given replaces the whole list, omitted it is kept. -/
def rowMergeJson (α : Type) [Entity α] (base : α) (j : Json) : Except DbError α := do
  let table := Entity.tableName α
  checkRowKeys α table j
  let cols ← ((columnsWithDerived α).zip (Entity.encode base)).mapM fun ((c, derived), old) => do
    if derived then return .null
    match ← rowValue? table j c with
    | some v =>
        match Col.fromJson c v with
        | .ok col => .ok col
        | .error m => .error (.decode table c.name m)
    | none => .ok old
  let a ← Entity.decodeRecomputing cols
  -- a child list given replaces the old one wholesale; omitted, it is kept
  (Entity.children (α := α)).foldlM (init := a) fun a link => do
    let rows ← match j.getObjVal? link.field with
      | .ok v => childRowsOfJson link v
      | .error _ => pure ((link.rows base).zipIdx.map fun (cols, i) => (i, cols))
    link.attachRecomputing rows a

end LeanDb
