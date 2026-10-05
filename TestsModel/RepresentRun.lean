/- Represented fields on both backends: the same programs give the same answers in memory and
   on SQLite, the stored value is the representation, and a stored value the checker rejects
   is a typed fault on each backend (a decode fault in memory, a corruption fault naming the
   column on SQLite), never a value. -/
import TestsModel.Represent
import TestsModel.Twin
open LeanDb.Model

native_schema% Bookings := Booking

namespace RepresentRun
open TestsModel RepresentFixture
open LeanDb (Read)
open LeanDb.Native (storageResources)

def tables : List (Table Bookings) := [.of Bookings Booking]

def wire {α} [Ontology.Wire α] (value : α) : String := (Ontology.Wire.codec.encode value).compress
def result (render : α → String) : Except BookError α → String
  | .ok value => "ok:" ++ render value
  | .error error => "error:" ++ reprStr error

/-- Replace one field of every stored `Booking` row (a corrupted or foreign write). -/
def tamper (store : Memory.Store) (field : String) (value : Lean.Json) : Memory.Store :=
  { store with rows := store.rows.map fun (key, json) =>
      if key.entity.name == "Booking" then (key, json.setObjVal! field value) else (key, json) }

def stored (column : String) : LeanDb.Db String :=
  LeanDb.untrackedSqlite fun db => do
    let stmt ← db.prepare s!"SELECT {LeanDb.quoteIdent column} FROM \"booking\" WHERE id = 1"
    if ← stmt.step then stmt.columnText 0 else return ""

def run : IO Unit := do
  let room ← parse "room" (Name.parse "Lab")
  let booking ← parse "ref" (Ontology.Ref.parse (T := Booking) "1")
  -- Memory, through the portable programs; inputs and outputs are the represented types.
  let some (created, store) := (Memory.run (book room (interval 2 5) (sorted [1, 3, 3]))).toOption
    | throw (IO.userError "FAIL: book in memory")
  let .ok created := created | throw (IO.userError "FAIL: booked")
  unless created == booking do throw (IO.userError "FAIL: booked")
  let .ok (some view, _) := Memory.run (showBooking booking) store | throw (IO.userError "FAIL: show")
  unless view.slot == interval 2 5 && view.seats == sorted [1, 3, 3] do throw (IO.userError "FAIL: round trip")
  let row := store.rows.find? (·.1.entity.name == "Booking") |>.map (·.2)
  unless row.map (fun json => (json.getObjValD "slot", json.getObjValD "seats")) ==
      some (.arr #[.num 2, .num 5], .arr #[.num 1, .num 3, .num 3]) do
    throw (IO.userError "FAIL: stored as the representation")
  match Memory.run (showBooking booking) (tamper store "slot" (.arr #[.num 9, .num 1])) with
  | .error (.decode errors) =>
    unless errors.first.code == "decode.invalid_representation" && errors.first.params.lookup "type" == some "Interval" &&
        errors.first.params.lookup "check" == some "Interval.check" do
      throw (IO.userError "FAIL: the decode fault names the type and checker")
  | _ => throw (IO.userError "FAIL: a rejected stored interval was read as a value")
  match Memory.run (showBooking booking) (tamper store "seats" (.arr #[.num 4, .num 2])) with
  | .error (.decode errors) =>
    unless errors.first.params.lookup "check" == some "SortedList.ofList?" do throw (IO.userError "FAIL: list checker")
  | _ => throw (IO.userError "FAIL: a rejected stored list was read as a value")
  -- Both backends.
  scenario Bookings "represent" do
    let booked ← command tables "book" (result fun r => r.key) (book room (interval 2 5) (sorted [1, 3, 3]))
      (book.withResources book.Requirements.infer room (interval 2 5) (sorted [1, 3, 3]))
    check (booked == "ok:1") s!"book: {booked}"
    let long ← command tables "book too long" (result fun r => r.key) (book room (interval 1 20) (sorted []))
      (book.withResources book.Requirements.infer room (interval 1 20) (sorted []))
    check (long == "error:BookError.tooLong") s!"too long: {long}"
    let shown ← query tables "showBooking" (fun v => (v.map fun v => wire v).getD "none") (showBooking booking)
      (showBooking.withResources showBooking.Requirements.infer booking)
    check (shown == "{\"seats\":[1,3,3],\"slot\":[2,5]}") s!"show: {shown}"
    check ((← stored "slot") == "[2,5]" && (← stored "seats") == "[1,3,3]") "stored as the representation's canonical JSON"
    -- A stored interval the checker rejects is a corruption fault naming the column.
    let _ ← LeanDb.untrackedSqlite fun db => db.exec "UPDATE \"booking\" SET slot = '[9,1]' WHERE id = 1"
    match ← LeanDb.Native.runQuery (showBooking.withResources (resources := storageResources Bookings)
        showBooking.Requirements.infer booking) with
    | .error (.corruption message) => check (message.startsWith "booking.slot:") s!"corruption names the column: {message}"
    | .error fault => fail s!"wrong fault: {fault}"
    | .ok _ => fail "a rejected stored interval was read as a value"
  IO.println "represent on memory and SQLite: round trip as the representation, checked reads, typed corruption PASS"

end RepresentRun
