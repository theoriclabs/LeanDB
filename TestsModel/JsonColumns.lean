import TestsModel.Twin
import LeanDb.Typed.Gate

/- Structured values in one column: a model entity field whose type is a list of
records, or a record, is stored as one TEXT column holding the canonical JSON of
its `StorageCodec`, and decoded through that codec on every read. A kitchen
domain, unrelated to any app, built from public API only; its programs run on
SQLite, every step compared with its pure meaning on the full state, counters
included. -/

open LeanDb.Model LeanDb.Native
open LeanDb (Txn Read DbState)

namespace JsonColumnFixture

inductive Dish where
  | soup | salad | pie
  deriving Domain

inductive Portion where
  | half | full
  deriving Domain

inductive Zone where
  | pickup | north | south
  deriving Domain

structure Line where
  dish    : Dish
  portion : Portion
  deriving Domain

structure Address where
  zone : Zone
  door : Nat
  deriving Domain

deriving instance BEq for Dish
deriving instance BEq for Portion
deriving instance BEq for Zone
deriving instance BEq for Line
deriving instance BEq for Address

/-! ## Before orders had a delivery address -/

namespace V1
structure Order where
  customer : Name
  lines    : List Line
  deriving Entity

native_schema% KitchenV1 := Order
end V1

/-! ## The current domain -/

structure Order where
  customer  : Name
  lines     : List Line
  deliverTo : Address
  deriving Entity

entity_operations Order
native_schema% Kitchen := Order

/-- Orders taken before delivery existed are picked up at the counter. -/
migration% addDelivery := Order.addField deliverTo (fill := Address.mk .pickup 0)

/-! ## A later, incompatible change to the stored line schema -/

inductive Heat where
  | mild | hot
  deriving Domain

namespace V3
structure Line where
  dish    : Dish
  portion : Portion
  heat    : Heat
  deriving Domain

structure Order where
  customer  : Name
  lines     : List Line
  deliverTo : Address
  deriving Entity

native_schema% KitchenV3 := Order
end V3

/-! ## Programs -/

def placeOrder (customer : Name) (lines : List Line) (deliverTo : Address) : DB (Ref Order) :=
  Order.insert { customer, lines, deliverTo }

def addLine (order : Ref Order) (line : Line) : DB Unit := do
  let some o ← Order.find order | pure ()
  Order.update o { o.toOrder with lines := o.lines ++ [line] }

def orderLines (order : Ref Order) : Query (Option (List Line)) := do
  return (← Order.find order).map (·.lines)

derive_requirements placeOrder, addLine, orderLines

abbrev R := storageResources Kitchen

/-! ## Full-state comparison with the pure meaning -/

def same (a b : DbState Kitchen) : Bool :=
  let left := a.get (α := Order)
  let right := b.get (α := Order)
  left.next == right.next && left.rows.length == right.rows.length &&
    (left.rows.zip right.rows).all fun (x, y) =>
      x.id == y.id && LeanDb.Entity.encode x.val == LeanDb.Entity.encode y.val

open TestsModel (fail check)
open TestsModel.Native (wire)

def command {A : Type} [Ontology.Wire A] (program : {σ : Type} → Program R .command σ A) (label : String) :
    LeanDb.Db String :=
  return (← TestsModel.Native.command same wire program label).1

def query {A : Type} [Ontology.Wire A] (program : Program R .query Unit A) (label : String) : LeanDb.Db String :=
  TestsModel.Native.query same wire program label

/-- The raw stored text of one column. -/
def stored (column : String) (id : Int64) : LeanDb.Db String :=
  LeanDb.untrackedSqlite fun db => do
    let stmt ← db.prepare s!"SELECT {LeanDb.quoteIdent column} FROM \"order\" WHERE id = ?"
    stmt.bindInt64 1 id
    if ← stmt.step then stmt.columnText 0 else return ""

/-- Corrupt one stored value with raw SQL; the next read must be a typed fault. -/
def corruptRead (column text : String) (expectedPrefix : String) : LeanDb.Db Unit := do
  let _ ← LeanDb.untrackedSqlite fun db => do
    let stmt ← db.prepare s!"UPDATE \"order\" SET {LeanDb.quoteIdent column} = ? WHERE id = 1"
    stmt.bindText 1 text
    stmt.exec
  let .ok id := idToRef (T := Order) ⟨1⟩ | fail "ref"
  match ← runQuery (orderLines.withResources (resources := R) orderLines.Requirements.infer id) with
  | .error (.corruption message) =>
      check (message.startsWith expectedPrefix) s!"corruption names the column: {message}"
  | .error fault => fail s!"wrong fault for {text}: {fault}"
  | .ok _ => fail s!"a stored {text} was read as a value"

def parse {α} (label : String) (result : Ontology.Validation α) : IO α :=
  match result with
  | .ok value => pure value
  | .error _ => throw (IO.userError s!"fixture value {label}")

def run : IO Unit := do
  IO.FS.createDirAll ".lake/ddd-m2-scratch"
  let nonce ← IO.monoNanosNow
  let path : System.FilePath := s!".lake/ddd-m2-scratch/leandb-json-runtime-{nonce}.sqlite"
  let ana ← parse "Ana" (Name.parse "Ana")
  let bo ← parse "Bo" (Name.parse "Bo")
  let cai ← parse "Cai" (Name.parse "Cai")
  let soupHalf : Line := ⟨.soup, .half⟩
  let pieFull : Line := ⟨.pie, .full⟩
  let saladFull : Line := ⟨.salad, .full⟩
  -- 1. A database from before delivery addresses, with list-of-record columns.
  match ← LeanDb.withDb path (LeanDb.IsSchema.specs V1.KitchenV1) do
    discard <| LeanDb.insert V1.Order ⟨ana, [soupHalf, pieFull]⟩
    discard <| LeanDb.insert V1.Order ⟨bo, []⟩
  with
  | .error e => throw (IO.userError s!"seed: {e}")
  | .ok () => pure ()
  -- 2. Adding a structured field needs a fill, like any required field.
  let target := LeanDb.Gate.Target.ofSchema Kitchen
  let raw ← match ← LeanDb.openDbRaw path with
    | .ok conn => pure conn
    | .error e => throw (IO.userError s!"raw: {e}")
  match ← LeanDb.Gate.check raw target [] with
  | .ok (.refused [.missingFill "Order" "order" "deliverTo"]) => pure ()
  | .ok status => throw (IO.userError s!"expected the deliverTo refusal:\n{status.render}")
  | .error e => throw (IO.userError s!"check: {e}")
  let conn ← match ← LeanDb.Gate.openDb path target [addDelivery] with
    | .ok (conn, .applied ..) => pure conn
    | _ => throw (IO.userError "the delivery migration did not apply")
  -- 3. A changed stored schema (a field added to `Line`) is refused by name.
  match ← LeanDb.Gate.check conn (LeanDb.Gate.Target.ofSchema V3.KitchenV3) [] with
  | .ok (.refused findings) =>
      unless findings.any (fun f => (f.render.splitOn "stores a structured value whose schema changed").length > 1) do
        throw (IO.userError s!"unexpected refusal: {(LeanDb.Gate.Status.refused findings).render}")
  | .ok status => throw (IO.userError s!"a changed JSON schema was accepted:\n{status.render}")
  | .error e => throw (IO.userError s!"check v3: {e}")
  match ← LeanDb.DbM.run conn (show LeanDb.Db Unit from do
    let spec := LeanDb.Entity.spec Order
    check (spec.columns.all fun c => c.name == "customer" ||
      (c.sqlType == .text && (c.shape.any (·.startsWith "wire:")))) "structured fields are TEXT with a wire shape"
    let migrated ← DbState.load (s := Kitchen)
    let orders := (migrated.get (α := Order)).rows
    check (orders.map (fun o => (o.val.lines, o.val.deliverTo)) ==
      [([soupHalf, pieFull], ⟨.pickup, 0⟩), ([], ⟨.pickup, 0⟩)]) "old orders keep their lines and take the fill"
    check ((← stored "lines" 1) == wire [soupHalf, pieFull] && (← stored "deliverTo" 1) == wire (Address.mk .pickup 0))
      "the stored text is the canonical JSON"
    -- 4. Insert and read through the model programs.
    let placed ← command (placeOrder.withResources placeOrder.Requirements.infer cai [saladFull] ⟨.north, 12⟩) "placeOrder"
    check (placed == "ok:3") s!"placeOrder: {placed}"
    let .ok third := idToRef (T := Order) ⟨3⟩ | fail "ref"
    let read ← query (orderLines.withResources orderLines.Requirements.infer third) "orderLines"
    check (read == "ok:" ++ wire (some [saladFull])) s!"lines read back: {read}"
    -- 5. Update round trip: the whole new list is written and read back.
    let .ok first := idToRef (T := Order) ⟨1⟩ | fail "ref"
    let added ← command (addLine.withResources addLine.Requirements.infer first saladFull) "addLine"
    check (added == "ok:" ++ wire ()) s!"addLine: {added}"
    let read ← query (orderLines.withResources orderLines.Requirements.infer first) "orderLines after update"
    check (read == "ok:" ++ wire (some [soupHalf, pieFull, saladFull])) s!"updated lines: {read}"
    check ((← stored "lines" 1) == wire [soupHalf, pieFull, saladFull]) "the updated text is canonical"
    -- 6. Corruption is a typed fault naming the column, never a value.
    corruptRead "lines" "not json" "order.lines:"
    corruptRead "lines" "[{\"dish\":\"cake\",\"portion\":\"full\"}]" "order.lines:"
    corruptRead "lines" "[{\"dish\":\"soup\"}]" "order.lines:"
  ) with
  | .error e => throw (IO.userError e.message)
  | .ok () => pure ()
  -- A record value with an unknown field is refused too (a fresh row 1 state).
  match ← LeanDb.DbM.run conn (show LeanDb.Db Unit from do
    let _ ← LeanDb.untrackedSqlite fun db =>
      db.exec "UPDATE \"order\" SET lines = '[]', deliverTo = '{\"zone\":\"north\",\"door\":1,\"floor\":2}' WHERE id = 1"
    match ← Read.run (Read.get (s := Kitchen) Order ⟨1⟩) with
    | .error (.corruption message) =>
        check (message.startsWith "order.deliverTo:") s!"record corruption names the column: {message}"
    | .error fault => fail s!"wrong fault: {fault}"
    | .ok _ => fail "a record with an unknown field was read as a value"
  ) with
  | .error e => throw (IO.userError e.message)
  | .ok () => IO.println "structured values in one column: list and record fields, migration fill, schema-change refusal, update round trip, typed corruption PASS"

end JsonColumnFixture
