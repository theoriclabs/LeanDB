/- A twin harness: every step of a scenario runs on the in-memory backend AND on SQLite, and
   must give the same answer (or the same fault code) on both. The SQLite run is also compared
   with its pure meaning (`Txn.denote`/`Read.denote`) on the full state, and after every step
   each table (ids, row JSON and identity counter) must be the same on both backends. The
   in-memory side runs the portable program (`f args : DB α`); the SQLite side runs the same
   definition generalized by `derive_requirements` at the native family
   (`f.withResources f.Requirements.infer args`). -/
import LeanDb.Native

namespace TestsModel
open LeanDb.Model
open LeanDb (DbState Txn Read)
open LeanDb.Native (StorageFault storageResources runCommand runQuery)

/-- One entity's table, as both backends hold it: identity counter, then (id, row JSON). -/
structure Table (S : Type) [LeanDb.IsSchema S] where
  name : String
  memory : Memory.Store → Nat × List (String × String)
  native : DbState S → Nat × List (String × String)

def Table.of (S T : Type) [LeanDb.IsSchema S] [LeanDb.Model.Entity T] [LeanDb.Entity T]
    [LeanDb.IsSchema.Has S T] : Table S where
  name := (Ontology.HasTypeId.typeId (α := T)).name
  memory store :=
    let identity := Ontology.HasTypeId.typeId (α := T)
    let rows := store.rows.filter (·.1.entity == identity)
      |>.mergeSort (fun a b => a.1.id.toNat?.getD 0 ≤ b.1.id.toNat?.getD 0)
    ((store.next.find? (·.1 == identity)).map Prod.snd |>.getD 1, rows.map fun (key, json) => (key.id, json.compress))
  native state :=
    let table := state.get (α := T)
    (table.next, table.rows.map fun row =>
      (toString row.id.toInt64.toInt, ((Entity.recordRepresentation (T := T)).encode row.val).compress))

abbrev TwinM := StateT Memory.Store LeanDb.Db

def fail (label : String) : LeanDb.Db α := throw (.sqlite s!"check failed: {label}")
def check (ok : Bool) (label : String) : LeanDb.Db Unit := unless ok do fail label

/-- Both backends hold the same tables. -/
def sameTables {S : Type} [LeanDb.IsSchema S] (tables : List (Table S)) (label : String) : TwinM Unit := do
  let store ← get
  let state ← DbState.load (s := S)
  for table in tables do
    let memory := table.memory store
    let native := table.native state
    check (memory == native) s!"{label}: table {table.name} differs: memory {memory} vs SQLite {native}"

private def nativeOutcome (render : α → String) : Except StorageFault α → String
  | .ok value => render value
  | .error fault => "fault:" ++ fault.code

/-- One read-write step on both backends. A fault discards the in-memory writes, as it rolls
back the SQLite transaction. -/
def command {S : Type} [LeanDb.IsSchema S] (tables : List (Table S)) (label : String) (render : α → String)
    (portable : DB α) (native : {σ : Type} → Program (storageResources S) .command σ α) : TwinM String := do
  let store ← get
  let (memory, after) := match Memory.run portable store with
    | .ok (value, after) => (render value, after)
    | .error fault => ("fault:" ++ fault.code, store)
  let before ← DbState.load (s := S)
  check before.checkWF s!"{label}: well-formed before"
  let meaning := Txn.denote (LeanDb.Native.Program.toTxn (native (σ := Unit))) before
  let actual ← match ← runCommand native with
    | .ok actual => pure actual
    | .error fault => fail s!"{label}: executor fault {fault}"
  let answer := nativeOutcome render actual
  check (answer == nativeOutcome render meaning.1) s!"{label}: SQLite {answer} vs its meaning {nativeOutcome render meaning.1}"
  check (answer == memory) s!"{label}: SQLite {answer} vs memory {memory}"
  let now ← DbState.load (s := S)
  check now.checkWF s!"{label}: well-formed after"
  for table in tables do
    check (table.native now == table.native meaning.2) s!"{label}: table {table.name} differs from the meaning"
  set after
  sameTables tables label
  return answer

/-- One read-only step on both backends; neither writes. -/
def query {S : Type} [LeanDb.IsSchema S] (tables : List (Table S)) (label : String) (render : α → String)
    (portable : Query α) (native : Program (storageResources S) .query Unit α) : TwinM String := do
  let store ← get
  let memory := match Memory.run portable store with
    | .ok (value, _) => render value
    | .error fault => "fault:" ++ fault.code
  let before ← DbState.load (s := S)
  let meaning := Read.denote (LeanDb.Native.Program.toRead native) before
  let actual ← match ← runQuery native with
    | .ok actual => pure actual
    | .error fault => fail s!"{label}: executor fault {fault}"
  let answer := nativeOutcome render actual
  check (answer == nativeOutcome render meaning) s!"{label}: SQLite {answer} vs its meaning {nativeOutcome render meaning}"
  check (answer == memory) s!"{label}: SQLite {answer} vs memory {memory}"
  sameTables tables label
  return answer

/-- Run a scenario on a fresh SQLite file and an empty in-memory store. -/
def scenario (S : Type) [LeanDb.IsSchema S] (name : String) (body : TwinM Unit) : IO Unit := do
  IO.FS.createDirAll ".lake/ddd-m2-scratch"
  let nonce ← IO.monoNanosNow
  let path : System.FilePath := s!".lake/ddd-m2-scratch/leandb-model-{name}-{nonce}.sqlite"
  match ← LeanDb.withDb path (LeanDb.IsSchema.specs S) (body.run' {}) with
  | .ok () => pure ()
  | .error e => throw (IO.userError s!"{name}: {e.message}")

def parse {α} (label : String) (result : Ontology.Validation α) : IO α :=
  match result with
  | .ok value => pure value
  | .error _ => throw (IO.userError s!"fixture value {label}")


/-! ## SQLite alone (after a native migration, which the in-memory store does not follow) -/

namespace Native
open LeanDb.Native (StorageFault storageResources runCommand runQuery)
open LeanDb (DbState Txn Read)

def wire {α} [Ontology.Wire α] (value : α) : String := (Ontology.Wire.codec.encode value).compress

/-- `ok:<wire value>`, or `storage:<fault code>[:<constraint>]`. -/
def render {A : Type} (display : A → String) : Except StorageFault A → String
  | .ok value => "ok:" ++ display value
  | .error fault => "storage:" ++ fault.code ++
      (match fault with
        | .restricted c | .missingReference c | .unmappedConflict c => ":" ++ c.identity
        | _ => "")

/-- One read-write step on SQLite, compared with its meaning on the full state. -/
def command {S A : Type} [LeanDb.IsSchema S] (same : DbState S → DbState S → Bool) (display : A → String)
    (program : {σ : Type} → Program (storageResources S) .command σ A) (label : String) :
    LeanDb.Db (String × Except StorageFault A) := do
  let before ← DbState.load (s := S)
  check before.checkWF (label ++ ": WF before")
  let meaning := Txn.denote (LeanDb.Native.Program.toTxn (program (σ := Unit))) before
  match ← runCommand program with
  | .error fault => fail s!"{label}: executor fault {fault}"
  | .ok actual =>
      let after ← DbState.load (s := S)
      check after.checkWF (label ++ ": WF after")
      check (render display actual == render display meaning.1)
        s!"{label}: answer {render display actual} vs meaning {render display meaning.1}"
      check (same after meaning.2) (label ++ ": every table and counter equals the meaning")
      return (render display actual, actual)

/-- One read-only step on SQLite, compared with its meaning; it writes nothing. -/
def query {S A : Type} [LeanDb.IsSchema S] (same : DbState S → DbState S → Bool) (display : A → String)
    (program : Program (storageResources S) .query Unit A) (label : String) : LeanDb.Db String := do
  let before ← DbState.load (s := S)
  let meaning := Read.denote (LeanDb.Native.Program.toRead program) before
  match ← runQuery program with
  | .error fault => fail s!"{label}: executor fault {fault}"
  | .ok actual =>
      check (render display actual == render display meaning)
        s!"{label}: answer {render display actual} vs meaning {render display meaning}"
      check (same before (← DbState.load (s := S))) (label ++ ": a read writes nothing")
      return render display actual

end Native
end TestsModel
