import LeanApp.Domain
import LeanDbDomain
import LeanDb.Typed.Gate

/- A represented private-constructor type as an entity field. `Slot` can only be
built with `start < finish`; `represent Slot as Nat × Nat by … checked Slot.check`
gives it its codec, and LeanDB stores it as one column of that codec's canonical
JSON. Every read goes through `Slot.check`: a stored pair that fails it is a typed
corruption fault naming the table and column, and no `Slot` is ever built any
other way. A room-booking domain from public API only, run on SQLite through the
shared `Flow.run`, each step compared with its pure meaning on the full state. -/

open LeanApp.Domain LeanDb.Domain
open LeanDb (Txn Read DbState)

namespace RepresentFixture

/-- A time slot whose start precedes its finish. Only `Slot.make` and
    `Slot.check` build one. -/
structure Slot where
  private mk ::
  start  : Nat
  finish : Nat
  deriving BEq

def Slot.make (start finish : Nat) (_ : start < finish) : Slot := ⟨start, finish⟩

def Slot.toPair (slot : Slot) : Nat × Nat := (slot.start, slot.finish)

def Slot.check : Nat × Nat → Except String Slot
  | (start, finish) => if start < finish then .ok ⟨start, finish⟩ else .error "start must precede finish"

represent Slot as Nat × Nat by Slot.toPair checked Slot.check

inductive Aisle where
  | left | right
  deriving Domain

structure Seat where
  aisle  : Aisle
  number : Nat
  deriving Domain

deriving instance BEq for Aisle
deriving instance BEq for Seat

structure Booking where
  room  : Title
  slot  : Slot
  seats : List Seat
  deriving Entity

entity_operations Booking
native_schema% Rooms := Booking

def book (room : Title) (slot : Slot) (seats : List Seat) : Op Empty (Ref Booking) :=
  Booking.insert { room, slot, seats }

def moveTo (booking : Ref Booking) (slot : Slot) : Op Empty Unit := do
  let some b ← Booking.find booking | pure ()
  Booking.update b { b.toBooking with slot }

def slotOf (booking : Ref Booking) : ReadOp Empty (Option Slot) := do
  return (← Booking.find booking).map (·.slot)

derive_operation book
derive_operation moveTo
derive_operation slotOf

abbrev R := storageResources Rooms

def bookRequirements : book.Requirements R := book.Requirements.infer
def moveRequirements : moveTo.Requirements R := moveTo.Requirements.infer
def slotRequirements : slotOf.Requirements R := slotOf.Requirements.infer

/-! ## The test algebra (the requests these operations build) -/

def commandRequest {σ E A : Type} : RequestF R σ E .command A → Txn σ Rooms StorageFault A
  | @RequestF.find _ _ _ _ _ inst storage reference =>
      letI := inst
      match storage.find reference with
      | .error why => Txn.throw (.invalidReference why)
      | .ok read => Txn.ofRead read
  | @RequestF.insert _ _ _ _ _ inst storage value conflicts =>
      letI := inst
      storage.insert value conflicts id
  | @RequestF.update _ _ _ _ _ inst storage row patch conflicts =>
      letI := inst
      storage.update row patch conflicts id
  | _ => Txn.throw (.invalidReference "unsupported request")

def runOp {E A : Type} (flow : {σ : Type} → Flow .command σ E A R) :
    {σ : Type} → Txn σ Rooms StorageFault (Except E A) :=
  Flow.run { request := fun request => do return .ok (← commandRequest request)
             contains := fun _ _ => Txn.throw (StorageFault.invalidReference "contains")
             project := fun _ => Txn.throw (StorageFault.invalidReference "project") } flow

def queryRequest {E A : Type} : RequestF R Unit E .query A → ExceptT StorageFault (Read Rooms) A
  | @RequestF.find _ _ _ _ _ inst storage reference =>
      letI := inst
      match storage.find reference with
      | .error why => throw (.invalidReference why)
      | .ok read => liftM read
  | _ => throw (.invalidReference "unsupported request")

def runRead {E A : Type} (flow : Flow .query Unit E A R) : Read Rooms (Except StorageFault (Except E A)) :=
  (Flow.run { request := fun request => do return .ok (← queryRequest request)
              contains := fun _ _ => throw (StorageFault.invalidReference "contains")
              project := fun _ => throw (StorageFault.invalidReference "project") } flow).run

/-! ## Full-state comparison with the pure meaning -/

def same (a b : DbState Rooms) : Bool :=
  let left := a.get (α := Booking)
  let right := b.get (α := Booking)
  left.next == right.next && left.rows.length == right.rows.length &&
    (left.rows.zip right.rows).all fun (x, y) =>
      x.id == y.id && LeanDb.Entity.encode x.val == LeanDb.Entity.encode y.val

def fail (label : String) : LeanDb.Db α := throw (.sqlite s!"RepresentRuntime check failed: {label}")

def check (ok : Bool) (label : String) : LeanDb.Db Unit := unless ok do fail label

def wire {α} [Ontology.Wire α] (value : α) : String := (Ontology.Wire.codec.encode value).compress

def command {E A : Type} [Ontology.Wire E] [Ontology.Wire A]
    (flow : {σ : Type} → Flow .command σ E A R) (label : String) : LeanDb.Db String := do
  let program : {σ : Type} → Txn σ Rooms StorageFault (Except E A) := runOp flow
  let before ← DbState.load (s := Rooms)
  check before.checkWF (label ++ ": WF before")
  let expected := Txn.denote (program (σ := Unit)) before
  let show' : Except StorageFault (Except E A) → String
    | .ok (.ok value) => "ok:" ++ wire value
    | .ok (.error error) => "domain:" ++ wire error
    | .error fault => "storage:" ++ fault.code
  match ← Txn.run program with
  | .error fault => fail s!"{label}: executor fault {fault}"
  | .ok actual =>
      let after ← DbState.load (s := Rooms)
      check after.checkWF (label ++ ": WF after")
      check (show' actual == show' expected.1) s!"{label}: answer {show' actual} vs meaning {show' expected.1}"
      check (same after expected.2) (label ++ ": every table and counter equals the meaning")
      return show' actual

def query {E A : Type} [Ontology.Wire E] [Ontology.Wire A]
    (flow : Flow .query Unit E A R) (label : String) : LeanDb.Db String := do
  let program := runRead flow
  let before ← DbState.load (s := Rooms)
  let expected := Read.denote program before
  let show' : Except StorageFault (Except E A) → String
    | .ok (.ok value) => "ok:" ++ wire value
    | .ok (.error error) => "domain:" ++ wire error
    | .error fault => "storage:" ++ fault.code
  match ← Read.run program with
  | .error fault => fail s!"{label}: executor fault {fault}"
  | .ok actual =>
      check (show' actual == show' expected) s!"{label}: answer {show' actual} vs meaning {show' expected}"
      check (same before (← DbState.load (s := Rooms))) (label ++ ": a read writes nothing")
      return show' actual

def stored (column : String) : LeanDb.Db String :=
  LeanDb.untrackedSqlite fun db => do
    let stmt ← db.prepare s!"SELECT {LeanDb.quoteIdent column} FROM \"booking\" WHERE id = 1"
    if ← stmt.step then stmt.columnText 0 else return ""

/-- Write a stored value with raw SQL; the next read must be a typed fault. -/
def corruptRead (column text expectedPrefix : String) : LeanDb.Db Unit := do
  let _ ← LeanDb.untrackedSqlite fun db => do
    let stmt ← db.prepare s!"UPDATE \"booking\" SET {LeanDb.quoteIdent column} = ? WHERE id = 1"
    stmt.bindText 1 text
    stmt.exec
  let .ok booking := idToRef (T := Booking) ⟨1⟩ | fail "ref"
  match ← Read.run (runRead (slotOf.flowWithResources slotRequirements booking)) with
  | .error (.corruption message) =>
      check (message.startsWith expectedPrefix) s!"corruption names the column: {message}"
  | .error fault => fail s!"wrong fault for {text}: {fault}"
  | .ok _ => fail s!"a stored {text} was read as a value"

def main : IO Unit := do
  let nonce ← IO.monoNanosNow
  let path : System.FilePath := s!".lake/ddd-m2-scratch/leandb-represent-runtime-{nonce}.sqlite"
  let .ok lab := Title.parse "Lab" | throw (IO.userError "title")
  let morning := Slot.make 9 11 (by decide)
  let afternoon := Slot.make 14 16 (by decide)
  let seats : List Seat := [⟨.left, 3⟩, ⟨.right, 1⟩]
  let .ok (conn, _) ← LeanDb.Gate.openDb path (LeanDb.Gate.Target.ofSchema Rooms) []
    | throw (IO.userError "open")
  match ← LeanDb.DbM.run conn (show LeanDb.Db Unit from do
    let spec := LeanDb.Entity.spec Booking
    check (spec.columns.any fun c => c.name == "slot" && c.sqlType == .text &&
      c.shape.any (·.startsWith "wire:")) "the represented field is one TEXT column with a wire shape"
    let booked ← command (book.flowWithResources bookRequirements lab morning seats) "book"
    check (booked == "ok:1") s!"book: {booked}"
    check ((← stored "slot") == wire morning && (← stored "slot") == "[9,11]" && (← stored "seats") == wire seats)
      "stored as the representation's canonical JSON"
    let .ok booking := idToRef (T := Booking) ⟨1⟩ | fail "ref"
    let read ← query (slotOf.flowWithResources slotRequirements booking) "slotOf"
    check (read == "ok:" ++ wire (some morning)) s!"slot read back through Slot.check: {read}"
    let moved ← command (moveTo.flowWithResources moveRequirements booking afternoon) "moveTo"
    check (moved == "ok:" ++ wire ()) s!"moveTo: {moved}"
    let read ← query (slotOf.flowWithResources slotRequirements booking) "slotOf after update"
    check (read == "ok:" ++ wire (some afternoon) && (← stored "slot") == "[14,16]") s!"updated slot: {read}"
    -- A stored pair that fails `Slot.check`, a value of the wrong shape, and a bad
    -- list element are typed corruption faults naming the column.
    corruptRead "slot" "[16,14]" "booking.slot:"
    corruptRead "slot" "\"noon\"" "booking.slot:"
  ) with
  | .error e => throw (IO.userError e.message)
  | .ok () => pure ()
  match ← LeanDb.DbM.run conn (show LeanDb.Db Unit from do
    let _ ← LeanDb.untrackedSqlite fun db =>
      db.exec "UPDATE \"booking\" SET slot = '[14,16]', seats = '[{\"aisle\":\"middle\",\"number\":2}]' WHERE id = 1"
    match ← Read.run (Read.get (s := Rooms) Booking ⟨1⟩) with
    | .error (.corruption message) =>
        check (message.startsWith "booking.seats:") s!"list corruption names the column: {message}"
    | .error fault => fail s!"wrong fault: {fault}"
    | .ok _ => fail "a seat with an unknown aisle was read as a value"
  ) with
  | .error e => throw (IO.userError e.message)
  | .ok () => IO.println "represented private-constructor field and list-of-records field: canonical storage, checked reads, update round trip, typed corruption PASS"

end RepresentFixture

def main : IO Unit := RepresentFixture.main
