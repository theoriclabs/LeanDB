import TestsModel.Twin
import LeanDb.Typed.Gate

/- A represented private-constructor type as an entity field. `Slot` can only be
built with `start < finish`; `represent Slot as Nat × Nat by … checked Slot.check`
gives it its codec, and LeanDB stores it as one column of that codec's canonical
JSON. Every read goes through `Slot.check`: a stored pair that fails it is a typed
corruption fault naming the table and column, and no `Slot` is ever built any
other way. A room-booking domain from public API only; its programs run on
SQLite, each step compared with its pure meaning on the full state. -/

open LeanDb.Model LeanDb.Native
open LeanDb (Txn Read DbState)

namespace RepresentNative

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

def book (room : Title) (slot : Slot) (seats : List Seat) : DB (Ref Booking) :=
  Booking.insert { room, slot, seats }

def moveTo (booking : Ref Booking) (slot : Slot) : DB Unit := do
  let some b ← Booking.find booking | pure ()
  Booking.update b { b.toBooking with slot }

def slotOf (booking : Ref Booking) : Query (Option Slot) := do
  return (← Booking.find booking).map (·.slot)

derive_requirements book, moveTo, slotOf

abbrev R := storageResources Rooms

/-! ## Full-state comparison with the pure meaning -/

def same (a b : DbState Rooms) : Bool :=
  let left := a.get (α := Booking)
  let right := b.get (α := Booking)
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
  match ← runQuery (slotOf.withResources (resources := R) slotOf.Requirements.infer booking) with
  | .error (.corruption message) =>
      check (message.startsWith expectedPrefix) s!"corruption names the column: {message}"
  | .error fault => fail s!"wrong fault for {text}: {fault}"
  | .ok _ => fail s!"a stored {text} was read as a value"

def run : IO Unit := do
  IO.FS.createDirAll ".lake/ddd-m2-scratch"
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
    let booked ← command (book.withResources book.Requirements.infer lab morning seats) "book"
    check (booked == "ok:1") s!"book: {booked}"
    check ((← stored "slot") == wire morning && (← stored "slot") == "[9,11]" && (← stored "seats") == wire seats)
      "stored as the representation's canonical JSON"
    let .ok booking := idToRef (T := Booking) ⟨1⟩ | fail "ref"
    let read ← query (slotOf.withResources slotOf.Requirements.infer booking) "slotOf"
    check (read == "ok:" ++ wire (some morning)) s!"slot read back through Slot.check: {read}"
    let moved ← command (moveTo.withResources moveTo.Requirements.infer booking afternoon) "moveTo"
    check (moved == "ok:" ++ wire ()) s!"moveTo: {moved}"
    let read ← query (slotOf.withResources slotOf.Requirements.infer booking) "slotOf after update"
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

end RepresentNative
