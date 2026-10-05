import LeanDb
import TestsDddM2

namespace TestsDdd
open LeanDb

structure Person where
  name : String
  email : String
  deriving Repr, BEq, LeanDb.Entity
unique% Person.byEmail := email

inductive Visibility where
  | «public» | attendees | «private»
  deriving Repr, BEq, DecidableEq, LeanDb.ClosedEnum

structure Party where
  host : Ref Person
  title : String
  date : Int64
  visibility : Visibility
  deriving Repr, BEq, LeanDb.Entity

members% Party.guests : Person
schema% S := Person, Party

-- Physical unique alternatives remain distinguishable even for identical
-- column sets. Diagnostics must not select whichever IndexSpec appears first.
structure DuplicateColumns where
  email : String
  deriving LeanDb.Entity
unique% DuplicateColumns.first := email
unique% DuplicateColumns.second := email
schema% Diagnostics := DuplicateColumns

private def ck {α} [Entity α] (v : α) : DbM (Checked α) :=
  match Entity.check α v with
  | .ok checked => pure checked
  | .error why => throw (.invariant (Entity.tableName α) (toString (repr why.names)))

private def check (b : Bool) (label : String) : DbM Unit :=
  unless b do throw (.sqlite s!"DDD check failed: {label}")

private def stateEq (a b : DbState S) : Bool :=
  Harness.getEq (α := Person) a b && Harness.getEq (α := Party) a b &&
    Harness.getEq (α := Party.Guests) a b

private def concurrentIncludes (path : System.FilePath) (party : LeanDb.Id Party)
    (first second : LeanDb.Id Person) : IO Unit := do
  let start ← IO.mkRef false
  let .ok firstConnection ← openDb path (IsSchema.specs S)
    | throw (IO.userError "first member writer connection")
  let .ok secondConnection ← openDb path (IsSchema.specs S)
    | throw (IO.userError "second member writer connection")
  let worker (connection : Conn) (person : LeanDb.Id Person) := do
    while !(← start.get) do IO.sleep 1
    (Txn.run (s := S) (ε := String) (do
      let some row ← Txn.get Party party | Txn.throw "partyMissing"
      Txn.includeMember (Party.guestsRelation.bind row) person) connection).run
  let a ← IO.asTask (worker firstConnection first)
  let b ← IO.asTask (worker secondConnection second)
  start.set true
  for result in [← IO.ofExcept a.get, ← IO.ofExcept b.get] do
    match result with
    | .ok (.ok (.ok (.ok ()))) => pure ()
    | _ => throw (IO.userError "concurrent include failed")

private def compareTxn {α} [BEq α]
    (program : {σ : Type} → Txn σ S String α) (label : String)
    (execute : {σ : Type} → Txn σ S String α := program) : DbM (Except String α) := do
  let before ← DbState.load (s := S)
  Harness.requireWF before (label ++ ":before")
  let expected := Txn.denote (program (σ := Unit)) before
  match ← Txn.run execute with
  | .error fault => throw (.sqlite s!"{label}: unexpected fault {fault}")
  | .ok actual =>
      let after ← DbState.load (s := S)
      Harness.requireWF after (label ++ ":after")
      check (Harness.exceptEq (· == ·) (· == ·) actual expected.1) (label ++ ":result and failure payload")
      check (stateEq after expected.2) (label ++ ":all tables and counters")
      return actual

private def compareRead {α} [BEq α] (program : Read S α) (label : String) : DbM α := do
  let before ← DbState.load (s := S)
  let expected := Read.denote program before
  match ← Read.run program with
  | .error fault => throw (.sqlite s!"{label}: unexpected fault {fault}")
  | .ok actual =>
      check (actual == expected) (label ++ ":projection")
      check (stateEq before (← DbState.load (s := S))) (label ++ ":no writes")
      return actual

private def includeGuest (party : LeanDb.Id Party) (person : LeanDb.Id Person) : {σ : Type} → Txn σ S String Unit := do
  let some row ← Txn.get Party party | Txn.throw "partyMissing"
  (Txn.includeMember (Party.guestsRelation.bind row) person).orAbort
    (fun fk => "missingRef:" ++ toString (repr fk))

private def mutationDetected (party : LeanDb.Id Party) (person : LeanDb.Id Person) : DbM Bool :=
  fun conn => ExceptT.mk do
    -- Simulate the executor dropping an include primitive. The gate must fail
    -- on the final tables even though both successful answers are Unit.
    let result ← (compareTxn (includeGuest party person) "dropped include mutation"
      (Txn.pure ()) conn).run
    return .ok (match result with
      | .error (.sqlite message) => message == "DDD check failed: dropped include mutation:all tables and counters"
      | _ => false)

private def rename (party : LeanDb.Id Party) : {σ : Type} → Txn σ S String Unit := do
  let some row ← Txn.get Party party | Txn.throw "partyMissing"
  let value := { row.val with title := "changed" }
  match Entity.check Party value with
  | .error _ => Txn.throw "invalid"
  | .ok checked =>
      let _ ← (Txn.patch Party row (Fields.singleton Party.Field.title) checked).orAbort (fun _ => "patchFailed")
      pure ()

private def cancel (party : LeanDb.Id Party) : {σ : Type} → Txn σ S String Unit := do
  let _ ← (Txn.delete Party party).orAbort (fun _ => "deleteFailed")
  pure ()

private def setVisibility (party : LeanDb.Id Party) (visibility : Visibility) :
    {σ : Type} → Txn σ S String Unit := do
  let some row ← Txn.get Party party | Txn.throw "partyMissing"
  match Entity.check Party { row.val with visibility } with
  | .error _ => Txn.throw "invalid"
  | .ok checked =>
      let _ ← (Txn.patch Party row (Fields.singleton Party.Field.visibility) checked).orAbort (fun _ => "visibilityFailed")
      pure ()

private def deniedRead (party : LeanDb.Id Party) : Read S (Option (List String)) :=
  Read.discloseWith (.pure false)
    (.memberField Party.guestsRelation party Person.Field.name) some none

private def policy (visibility : Visibility) (actor : Option (LeanDb.Id Person)) (party : LeanDb.Id Party) : Read S Bool :=
  match visibility, actor with
  | .public, _ => .pure true
  | .attendees, some actor => .memberContains Party.guestsRelation party actor
  | _, _ => .pure false

private def pageNames (party : LeanDb.Id Party) (actor : Option (LeanDb.Id Person)) : Read S (Option (List String)) := do
  match ← Read.get Party party with
  | none => return none
  | some row =>
      Read.discloseWith (policy row.val.visibility actor party)
        (.memberField Party.guestsRelation party Person.Field.name) some none

/-- A controlled real visibility writer commits BETWEEN resource lookup and
    protected projection. The reader's enclosing snapshot still sees one
    consistent public state; the next snapshot sees private and hides it. -/
private def visibilityRace (path : System.FilePath) (party : LeanDb.Id Party) (names : List String) : IO Unit := do
  let .ok reader ← openDb path (IsSchema.specs S) | throw (IO.userError "race reader open")
  let .ok writer ← openDb path (IsSchema.specs S) | throw (IO.userError "race writer open")
  match ← (Txn.run (setVisibility party .public) writer).run with
  | .ok (.ok (.ok ())) => pure ()
  | _ => throw (IO.userError "race public setup")
  let lookedUp ← IO.mkRef false
  let committed ← IO.mkRef false
  let task ← IO.asTask do
    while !(← lookedUp.get) do IO.sleep 1
    let result ← (Txn.run (setVisibility party .private) writer).run
    committed.set true
    return result
  let result ← (readSnapshot (do
    let some row ← Read.exec (s := S) (.get Party party) | throw (.sqlite "race party missing")
    lookedUp.set true
    let mut remaining := 10000
    while !(← committed.get) && remaining > 0 do
      IO.sleep 1
      remaining := remaining - 1
    unless (← committed.get) do throw (.sqlite "visibility writer did not finish")
    Read.exec (Read.discloseWith (policy row.val.visibility none party)
      (.memberField Party.guestsRelation party Person.Field.name) some none)) reader).run
  match ← IO.ofExcept task.get with
  | .ok (.ok (.ok ())) => pure ()
  | _ => throw (IO.userError "visibility racing writer failed")
  match result with
  | .ok output => unless output == some names do throw (IO.userError "reader mixed visibility snapshots")
  | .error error => throw (IO.userError error.message)
  match ← (Read.run (pageNames party none) reader).run with
  | .ok (.ok none) => pure ()
  | _ => throw (IO.userError "subsequent private snapshot exposed names")

/-- Adding the generated pair index to legacy duplicate data must refuse the
    migration atomically; it cannot pick a surviving association. -/
private def duplicateMigration (nonce : Nat) : IO Unit := do
  let path : System.FilePath := s!"/tmp/leandb-ddd-duplicates-{nonce}.sqlite"
  let specs := IsSchema.specs S
  let legacy := specs.map fun spec =>
    if spec.name == Entity.tableName Party.Guests then
      { spec with indexes := spec.indexes.filter (! ·.unique) }
    else spec
  unless fingerprint specs != fingerprint legacy do
    throw (IO.userError "generated member index missing from schema fingerprint")
  match ← withDb path legacy do
    let person ← LeanDb.insert Person ⟨"Legacy", "legacy@example.test"⟩
    let _ ← LeanDb.insert Party ⟨person.id, "legacy", 1000, .public⟩
    untrackedSqlite fun db => db.exec "INSERT INTO party_guests(parent,target) VALUES (1,1),(1,1)"
  with
  | .error error => throw (IO.userError error.message)
  | .ok () => pure ()
  match ← migrate path specs (apply := true) with
  | .error (.migrate message) =>
      unless message.toLower.contains "unique constraint failed: party_guests.parent, party_guests.target" do
        throw (IO.userError s!"unexpected member migration refusal: {message}")
  | .error error => throw (IO.userError s!"wrong member migration error: {error.message}")
  | .ok _ => throw (IO.userError "duplicate member migration incorrectly succeeded")
  match ← withDb path legacy do
    let rows ← LeanDb.fetchAll Party.Guests
    check (rows.size == 2) "migration refusal preserves ALL duplicate rows"
  with
  | .error error => throw (IO.userError error.message)
  | .ok () => pure ()

def run : IO Unit := do
  let nonce ← IO.monoNanosNow
  unless (Unique.metadata (α := DuplicateColumns) DuplicateColumns.Unique.first).identity == "uq_duplicate_columns_first" &&
    (Unique.metadata (α := DuplicateColumns) DuplicateColumns.Unique.second).identity == "uq_duplicate_columns_second" do
    throw (IO.userError "typed constraint identities merged identical column sets")
  duplicateMigration nonce
  let path : System.FilePath := s!"/tmp/leandb-ddd-{nonce}.sqlite"
  match ← withDb path (IsSchema.specs S) do
    check ((IsSchema.specs S).length == 3) "association is in schema closure"
    let spec := Entity.spec Party.Guests
    check (spec.name == "party_guests") "stable parent/field table name"
    check (spec.columns[0]?.any (fun c => c.fkTable == some "party" && c.cascade)) "parent cascade FK"
    check (spec.columns[1]?.any (fun c => c.fkTable == some "person" && !c.cascade)) "target restrict FK"
    check (spec.indexes.any (fun i => i.unique && i.columns == #["parent", "target"])) "unique pair"
    check (spec.indexes.any (fun i => !i.unique && i.columns == #["target"])) "target index"
    check spec.fkIndexDdl.isEmpty "member edges need no engine FK index: both keys lead an index"
    let host ← LeanDb.insert Person ⟨"Host", "host@example.test"⟩
    let ada ← LeanDb.insert Person ⟨"Ada", "ada@example.test"⟩
    let grace ← LeanDb.insert Person ⟨"Grace", "grace@example.test"⟩
    let party ← LeanDb.insert Party ⟨host.id, "first", 1000, .attendees⟩
    let other ← LeanDb.insert Party ⟨host.id, "other", 1000, .public⟩
    let duplicate ← compareTxn (do
      let some row ← Txn.get Person ada.id | Txn.throw "personMissing"
      let .ok checked := Entity.check Person { row.val with email := host.val.email }
        | Txn.throw "invalidPerson"
      match ← Txn.patch Person row (Fields.singleton Person.Field.email) checked with
      | .error error@(.duplicate _ _) => return error.metadata?
      | .error _ => Txn.throw "unexpectedPatchFailure"
      | .ok _ => Txn.throw "duplicatePatchAccepted") "selective patch constraint metadata"
    check (Harness.exceptEq (· == ·) (· == ·) duplicate
      (.ok (some (Unique.metadata (α := Person) Person.Unique.byEmail))))
      "patch preserves exact unique identity and strips conflict holder"
    let denied0 ← compareRead (deniedRead party.id) "denied populated state"
    discard <| compareTxn (includeGuest party.id grace.id) "include Grace first"
    discard <| compareTxn (includeGuest party.id ada.id) "include Ada second"
    discard <| compareTxn (includeGuest party.id ada.id) "idempotent RSVP retry"
    discard <| compareTxn (includeGuest other.id host.id) "unrelated membership"
    let names ← compareRead (.memberField Party.guestsRelation party.id Person.Field.name) "target-ID order"
    check (names == ["Ada", "Grace"]) "nonempty visible witness and deterministic order"
    let (observedBefore, observedNames, observedAfter) ← Read.observe (s := S)
      (.memberField Party.guestsRelation party.id Person.Field.name)
    check (observedBefore.checkWF && observedAfter.checkWF && stateEq observedBefore observedAfter &&
      observedNames == names) "instrumented actual read observation on populated state"
    check (denied0 == (← compareRead (deniedRead party.id) "hidden memberships changed")) "hidden noninterference"
    check (← mutationDetected party.id host.id) "harness rejects dropped include executor mutation"
    check (← compareRead (.memberContains Party.guestsRelation party.id ada.id) "indexed contains") "stored member"
    let queryPlan ← untrackedSqlite fun db => do
      let stmt ← db.prepare ("EXPLAIN QUERY PLAN " ++ Read.memberContainsSql Party.guestsRelation)
      stmt.bindInt64 1 party.id.toInt64
      stmt.bindInt64 2 ada.id.toInt64
      let mut details := []
      while ← stmt.step do details := (← stmt.columnText 3) :: details
      return details
    check (queryPlan.any (fun line => line.contains "USING COVERING INDEX uq_party_guests_byPair"))
      "actual EXISTS query uses generated covering pair index"
    check (!(← compareRead (.memberContains Party.guestsRelation party.id host.id) "host not attendee")) "no host exception"
    check ((← compareRead (pageNames party.id (some host.id)) "attendee host without RSVP") == none) "host hidden"
    check ((← compareRead (pageNames party.id (some ada.id)) "attendee member") == some names) "attendee visible names only"
    for viewer in [none, some host.id, some ada.id] do
      check ((← compareRead (Read.discloseWith (policy .public viewer party.id)
        (.memberField Party.guestsRelation party.id Person.Field.name) some none) "public matrix") == some names) "public names"
      check ((← compareRead (Read.discloseWith (policy .private viewer party.id)
        (.memberField Party.guestsRelation party.id Person.Field.name) some none) "private matrix") == none) "private hidden including host"
    check ((← compareRead (pageNames party.id none) "anonymous attendee matrix") == none) "anonymous attendees hidden"
    -- The host is already an actual member of the other party. Private hides
    -- from that host too; use the stored visibility via the live page program.
    discard <| compareTxn (setVisibility other.id .private) "private host-member setup"
    check ((← compareRead (pageNames other.id (some host.id)) "private host with actual RSVP") == none)
      "private hides from host even when host is an attendee"
    discard <| compareTxn (setVisibility other.id .public) "restore other public visibility"
    visibilityRace path party.id names
    let missing ← compareTxn (includeGuest party.id ⟨999⟩) "missing target typed payload"
    check (Harness.exceptEq (· == ·) (· == ·) missing (.error "missingRef:TestsDdd.Party.Guests.ForeignKey.target")) "exact missing target alternative"
    let beforeAbort ← DbState.load (s := S)
    let aborted ← compareTxn (do
      includeGuest party.id host.id
      rename party.id
      Txn.throw "injectedFailure") "rollback after member and parent writes"
    check (Harness.exceptEq (· == ·) (· == ·) aborted (.error "injectedFailure" : Except String Unit)) "source-order abort payload"
    check (stateEq beforeAbort (← DbState.load (s := S))) "full rollback witness"
    let (abortBefore, abortResult, abortAfter) ← Txn.observe (s := S) (ε := String) (α := Unit) (do
      includeGuest party.id host.id
      rename party.id
      Txn.throw "observedAbort")
    check (Harness.exceptEq (· == ·) (· == ·) abortResult (.error "observedAbort") &&
      stateEq abortBefore abortAfter && stateEq abortBefore beforeAbort && abortAfter.checkWF)
      "instrumented writer observation sees actual rollback after two writes"
    let parentMissing ← compareTxn (do
      let some row ← Txn.get Party party.id | Txn.throw "partyMissing"
      cancel party.id
      (Txn.includeMember (Party.guestsRelation.bind row) ada.id).orAbort
        (fun fk => "missingRef:" ++ toString (repr fk))) "removed parent typed failure and rollback"
    check (Harness.exceptEq (· == ·) (· == ·) parentMissing (.error "missingRef:TestsDdd.Party.Guests.ForeignKey.parent")) "exact missing parent alternative"
    discard <| compareTxn (rename party.id) "field-limited update"
    check ((← compareRead (.memberField Party.guestsRelation party.id Person.Field.name) "members after patch") == names) "patch preserves members"
    check (Read.memberFieldSql Party.guestsRelation Person.Field.name |>.startsWith "SELECT t.\"name\"") "SQL selects names only"
    concurrentIncludes path other.id host.id host.id
    check (((← DbState.load (s := S)).get (α := Party.Guests)).rows.length == 3) "concurrent same-person retries leave one edge"
    concurrentIncludes path other.id ada.id grace.id
    check (((← DbState.load (s := S)).get (α := Party.Guests)).rows.length == 5) "distinct concurrent members remain"
    let restricted ← compareTxn (do
      match ← Txn.delete Person ada.id with
      | .error error@(.restricted who count) =>
        let some metadata := error.metadata? | Txn.throw "missingRestrictMetadata"
        if metadata.identity != "party_guests.foreignKey.target" || metadata.target != some "person" ||
            metadata.columns != #["target"] || metadata.cascade then
          Txn.throw "wrongRestrictMetadata"
        return (ReferencedBy.columnName who.val, count)
      | .error .gone => Txn.throw "unexpectedGone"
      | .ok _ => Txn.throw "targetDeleted") "member target deletion restricts"
    check (Harness.exceptEq (· == ·) (· == ·) restricted (.ok ("target", 2))) "typed restricting FK and row-count payload"
    let prepare : Db Nat := fun conn => ExceptT.mk do return .ok (← conn.txDepth.get)
    match ← Txn.runPrepared (s := S) (ε := String) prepare (fun depth => Txn.pure depth) with
    | .ok (.ok depth) => check (depth == 1) "environment sampled after BEGIN IMMEDIATE"
    | _ => throw (.sqlite "prepared runner failed")
    let deniedPlan : Read S (Option (List String)) := Read.discloseWith (.pure false)
      (Read.memberField Party.guestsRelation party.id Person.Field.email) some none
    -- Removing the physical relation causes any executed projection to fail.
    -- Hidden still succeeds, proving the executor does not even prepare it.
    discard <| compareTxn (cancel party.id) "parent deletion cascades only own edges"
    check (((← DbState.load (s := S)).get (α := Party.Guests)).rows.length == 3) "other party edges preserved"
    check (((← DbState.load (s := S)).get (α := Person)).rows.length == 3) "people preserved"
    let _ ← untrackedSqlite (fun db => db.exec "DROP TABLE party_guests")
    match ← Read.run deniedPlan with
    | .ok result => check (result == none) "hidden projection never executed"
    | .error fault => throw (.sqlite s!"hidden evaluated projection: {fault}")
  with
  | .error error => throw (IO.userError error.message)
  | .ok () => IO.println "DDD member-set differential/runtime checks passed"

end TestsDdd

def main : IO Unit := do
  TestsDdd.run
  TestsDddM2.run
