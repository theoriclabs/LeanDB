import TestsModel.Twin

/- A schema of twenty entities (#139). `schema%` generated `IsSchema.pack` as a `match` on
`Fin` literals, which Lean's match compiler refused as non-exhaustive ("Missing cases") from
the sixteenth entity on. Twenty model entities through `native_schema%` (which generates
`schema%`) must elaborate, create every table on SQLite, and write and read rows in the
first and the last table through both the engine verbs and the typed `Read`/`Txn` layer. -/

open LeanDb.Model

namespace WideSchemaFixture

structure E01 where
  label : Name
  deriving Entity

structure E02 where
  label : Name
  deriving Entity

structure E03 where
  label : Name
  deriving Entity

structure E04 where
  label : Name
  deriving Entity

structure E05 where
  label : Name
  deriving Entity

structure E06 where
  label : Name
  deriving Entity

structure E07 where
  label : Name
  deriving Entity

structure E08 where
  label : Name
  deriving Entity

structure E09 where
  label : Name
  deriving Entity

structure E10 where
  label : Name
  deriving Entity

structure E11 where
  label : Name
  deriving Entity

structure E12 where
  label : Name
  deriving Entity

structure E13 where
  label : Name
  deriving Entity

structure E14 where
  label : Name
  deriving Entity

structure E15 where
  label : Name
  deriving Entity

structure E16 where
  label : Name
  deriving Entity

structure E17 where
  label : Name
  deriving Entity

structure E18 where
  label : Name
  deriving Entity

structure E19 where
  label : Name
  deriving Entity

structure E20 where
  label : Name
  deriving Entity

native_schema% Wide := E01, E02, E03, E04, E05, E06, E07, E08, E09, E10,
  E11, E12, E13, E14, E15, E16, E17, E18, E19, E20

/-- Every table, in declaration order. -/
def tableNames : List String :=
  [LeanDb.Entity.tableName E01, LeanDb.Entity.tableName E02, LeanDb.Entity.tableName E03,
   LeanDb.Entity.tableName E04, LeanDb.Entity.tableName E05, LeanDb.Entity.tableName E06,
   LeanDb.Entity.tableName E07, LeanDb.Entity.tableName E08, LeanDb.Entity.tableName E09,
   LeanDb.Entity.tableName E10, LeanDb.Entity.tableName E11, LeanDb.Entity.tableName E12,
   LeanDb.Entity.tableName E13, LeanDb.Entity.tableName E14, LeanDb.Entity.tableName E15,
   LeanDb.Entity.tableName E16, LeanDb.Entity.tableName E17, LeanDb.Entity.tableName E18,
   LeanDb.Entity.tableName E19, LeanDb.Entity.tableName E20]

#guard LeanDb.IsSchema.nTables Wide == 20
#guard (LeanDb.IsSchema.specs Wide).map (·.name) == tableNames
#guard tableNames.eraseDups.length == 20

open TestsModel (fail check)

def parse {α} (label : String) (result : Ontology.Validation α) : IO α :=
  match result with
  | .ok value => pure value
  | .error _ => throw (IO.userError s!"fixture value {label}")

def run : IO Unit := do
  IO.FS.createDirAll ".lake/ddd-m2-scratch"
  let first ← parse "first" (Name.parse "first")
  let last ← parse "last" (Name.parse "last")
  let typed ← parse "typed" (Name.parse "typed")
  let nonce ← IO.monoNanosNow
  let path : System.FilePath := s!".lake/ddd-m2-scratch/leandb-wide-schema-{nonce}.sqlite"
  match ← LeanDb.withDb path (LeanDb.IsSchema.specs Wide) (show LeanDb.Db Unit from do
    -- Engine verbs on the first and the last table.
    discard <| LeanDb.insert E01 ⟨first⟩
    discard <| LeanDb.insert E20 ⟨last⟩
    -- The typed layer indexes tables through `IsSchema.pack`.
    let .ok checked := LeanDb.Entity.check E20 ⟨typed⟩ | fail "checked row"
    let program : {σ : Type} → LeanDb.Txn σ Wide String (LeanDb.Id E20) := do
      return (← LeanDb.Txn.insertNew (s := Wide) checked).id
    let before ← LeanDb.DbState.load (s := Wide)
    let expected := LeanDb.Txn.denote (program (σ := Unit)) before
    let inserted ← match ← LeanDb.Txn.run program with
      | .ok (.ok id) => pure id
      | _ => fail "typed insert into the last table"
    check (match expected.1 with | .ok id => id == inserted | .error _ => false)
      "typed insert agrees with its meaning"
    let after ← LeanDb.DbState.load (s := Wide)
    check (before.checkWF && after.checkWF) "states are well formed"
    let lastRows := (after.get (α := E20)).rows.map fun row => (row.id.toInt64.toInt, row.val.label.value)
    check (lastRows == [(1, "last"), (2, "typed")]) s!"last table rows: {lastRows}"
    check (lastRows == (expected.2.get (α := E20)).rows.map fun row => (row.id.toInt64.toInt, row.val.label.value))
      "last table matches the meaning"
    check ((after.get (α := E01)).rows.map (·.val.label.value) == ["first"]) "first table rows"
    check ((after.get (α := E10)).rows.isEmpty) "a middle table is empty"
    match ← LeanDb.Read.run (LeanDb.Read.get (s := Wide) E20 inserted) with
    | .ok (some row) => check (row.val.label.value == "typed") "read back the typed row"
    | _ => fail "typed read from the last table"
  ) with
  | .error error => throw (IO.userError error.message)
  | .ok () => IO.println "twenty-entity schema: elaborates, creates every table, writes and reads the first and last tables PASS"

end WideSchemaFixture
