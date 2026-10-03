import LeanDbDomain
import CheckAxioms

namespace DomainStorageFixture
open LeanApp.Domain

inductive Visibility where
  | «public» | attendees | «private»
  deriving Domain

@[entity] structure Person where
  name : Name
  email : Email

unique% Person.byEmail := email

@[entity] structure Party where
  host : Ref Person
  title : Title
  date : Instant
  description : Text
  visibility : Visibility := .public
  guests : Members Person := {}

native_schema% S := Person, Party

#synth LeanDb.Entity Person
#synth LeanDb.Entity Party
#synth LeanDb.IsSchema.Has S Party.Guests
#synth LeanDb.Domain.HasEntityStorage S Person
#synth LeanDb.Domain.HasEntityStorage S Party
#synth LeanDb.Domain.HasMemberStorage S Party "guests" Person
#synth LeanDb.Domain.HasFieldStorage S Person "name" Name
#synth LeanApp.Domain.HasEntityResource (LeanDb.Domain.storageResources S) Person
#synth LeanApp.Domain.HasMemberResource (LeanDb.Domain.storageResources S) Party "guests" Person

run_cmd do
  let uniqueDeclarations := (← Lean.getEnv).constants.toList.filter fun (_, info) =>
    info.type.isAppOfArity ``LeanApp.Domain.Unique 2 &&
      (info.type.getArg! 0).isConstOf ``Person
  unless uniqueDeclarations.length == 1 do
    throwError "expected exactly one original Person unique descriptor"
  for (name, _) in uniqueDeclarations do
    assertAxioms (name ++ `nativeFieldAgreement)
    assertAxioms (name ++ `nativeKeyAgreement)
  for scalar in [``Name, ``Title, ``Text, ``Email, ``Instant] do
    let law ← Lean.Elab.Command.liftTermElabM do
      let type := Lean.mkConst scalar
      let codec ← Lean.Meta.synthInstance (Lean.mkApp (Lean.mkConst ``LeanDb.ColCodec) type)
      Lean.Meta.synthInstance (Lean.mkApp2 (Lean.mkConst ``LeanDb.LawfulColCodec) type codec)
    assertAxioms law.getAppFn.constName!
  let law ← Lean.Elab.Command.liftTermElabM do
    let type := Lean.mkConst ``Party.Guests
    let entity ← Lean.Meta.synthInstance (Lean.mkApp (Lean.mkConst ``LeanDb.Entity) type)
    Lean.Meta.synthInstance (Lean.mkApp2 (Lean.mkConst ``LeanDb.LawfulEntity) type entity)
  assertAxioms law.getAppFn.constName!
  let field ← Lean.Elab.Command.liftTermElabM do
    let schema ← Lean.Meta.synthInstance (Lean.mkApp (Lean.mkConst ``LeanDb.IsSchema) (Lean.mkConst ``S))
    let entityStorage ← Lean.Meta.synthInstance (Lean.mkAppN (Lean.mkConst ``LeanDb.Domain.HasEntityStorage)
      #[Lean.mkConst ``S, Lean.mkConst ``Person, schema])
    Lean.Meta.synthInstance (Lean.mkAppN (Lean.mkConst ``LeanDb.Domain.HasFieldStorage)
      #[Lean.mkConst ``S, Lean.mkConst ``Person, Lean.mkStrLit "name", Lean.mkConst ``Name, schema, entityStorage])
  assertAxioms field.getAppFn.constName!

-- This uses the generated existential Edge without naming Party.Guests or
-- creating a manual storage witness at the application assembly site.
def witnessedContains (party : LeanDb.Id Party) (person : LeanDb.Id Person) : LeanDb.Read S Bool :=
  let storage := (LeanApp.Domain.HasMemberResource.witness
    (family := LeanDb.Domain.storageResources S) (P := Party) (field := "guests") (T := Person))
  letI := storage.parent.entity
  letI := storage.target.entity
  letI := storage.edge.entity
  letI := storage.edge.unique
  letI := storage.edge.foreignKey
  letI := storage.edge.schema
  LeanDb.Read.memberContains storage.relation party person

def witnessedNames (party : LeanDb.Id Party) : LeanDb.Read S (List Name) :=
  let members := (LeanDb.Domain.HasMemberStorage.storage (s := S) (Parent := Party)
    (field := "guests") (Target := Person))
  letI := members.parent.entity
  letI := members.target.entity
  letI := members.edge.entity
  letI := members.edge.unique
  letI := members.edge.foreignKey
  letI := members.edge.schema
  letI := members.target.schema
  let column := LeanDb.Domain.HasFieldStorage.storage (s := S) (T := Person) (field := "name") (Value := Name)
  column.project members.relation party

private def assertCheck (value : Bool) (label : String) : IO Unit :=
  unless value do throw (IO.userError label)

private def concurrentCanonical (path : System.FilePath) (name : Name) : IO Unit := do
  let start ← IO.mkRef false
  -- Connection/schema setup is completed before racing the actual writers.
  -- Racing bootstrap metadata is a different operation from canonical signup.
  let .ok firstConnection ← LeanDb.openDb path (LeanDb.IsSchema.specs S)
    | throw (IO.userError "first canonical writer connection")
  let .ok secondConnection ← LeanDb.openDb path (LeanDb.IsSchema.specs S)
    | throw (IO.userError "second canonical writer connection")
  let worker (connection : LeanDb.Conn) (raw : String) := do
    let .ok email := Email.parse raw | throw (IO.userError "concurrent canonical parse")
    let .ok checked := LeanDb.Entity.check Person ⟨name, email⟩
      | throw (IO.userError "concurrent canonical storage check")
    while !(← start.get) do IO.sleep 1
    (LeanDb.Txn.run (s := S) (ε := String) (do
        match ← LeanDb.Txn.insert Person checked with
        | .ok _ => return true
        | .error error@(.duplicate _ _) =>
            if error.metadata.identity == "uq_person_byEmail" then return false
            else LeanDb.Txn.throw "wrong constraint"
        | .error (.missingRef fk) => nomatch fk) connection).run
  let first ← IO.asTask (worker firstConnection "Next@Example.test")
  let second ← IO.asTask (worker secondConnection " next@example.test ")
  start.set true
  let mut outcomes := []
  for result in [← IO.ofExcept first.get, ← IO.ofExcept second.get] do
    match result with
    | .ok (.ok (.ok outcome)) => outcomes := outcome :: outcomes
    | .error error => throw (IO.userError s!"concurrent open: {error.message}")
    | .ok (.error fault) => throw (IO.userError s!"concurrent storage fault: {fault.message}")
    | .ok (.ok (.error error)) => throw (IO.userError s!"concurrent domain error: {error}")
  assertCheck (outcomes.count true == 1 && outcomes.count false == 1)
    "concurrent canonical variants create exactly one profile and one typed duplicate"
  match ← LeanDb.withDb path (LeanDb.IsSchema.specs S) do
    let profiles ← LeanDb.fetchAll Person
    unless (profiles.filter (·.val.email.value == "next@example.test")).size == 1 do
      throw (.sqlite "canonical race left duplicate profiles")
  with
  | .error error => throw (IO.userError error.message)
  | .ok () => pure ()

def main : IO Unit := do
  let .ok ada := Name.parse " Ada " | throw (IO.userError "name parse")
  let .ok email := Email.parse " Ada@Example.test " | throw (IO.userError "email parse")
  let .ok email2 := Email.parse "ada@example.test" | throw (IO.userError "email parse 2")
  assertCheck (email == email2) "canonical Email parser"
  assertCheck (LeanDb.toCol email == .text "ada@example.test") "canonical storage"
  assertCheck ((LeanDb.fromCol (α := Email) (.text "broken")).toOption.isNone) "decode invalid email"
  assertCheck ((LeanDb.fromCol (α := Name) (.text "  ")).toOption.isNone) "decode invalid name"
  assertCheck ((LeanDb.fromCol (α := Ref Person) (.int 0)).toOption.isNone) "decode nonpositive ref"
  let .ok personRef := Ref.parse (T := Person) "9223372036854775807" | throw (IO.userError "max ref")
  let .ok id := LeanDb.Domain.refToId personRef | throw (IO.userError "checked ref to native")
  assertCheck (id.toInt64 == Int64.maxValue) "signed-64 max reference"
  assertCheck ((Ref.parse (T := Person) "9223372036854775808").toOption.isNone) "out-of-range ref"
  let .ok otherScopeRef := Ref.parse (T := Person) "1" "other" | throw (IO.userError "scope parse")
  assertCheck ((LeanDb.Domain.refToId otherScopeRef).toOption.isNone) "ref scope mismatch"
  assertCheck ((LeanDb.toSql? otherScopeRef).isNone) "scope mismatch cannot be checked storage"
  let .ok maxInstant := Instant.ofEpochSeconds int64Max | throw (IO.userError "max instant")
  assertCheck (LeanDb.toCol maxInstant == .int Int64.maxValue) "Instant signed-64 max"
  assertCheck ((Instant.ofEpochSeconds (int64Max + 1)).toOption.isNone) "Instant overflow"
  assertCheck ((LeanDb.IsSchema.specs S).length == 3) "automatic association closure"
  assertCheck ((LeanDb.Entity.columns Party).size == 5) "Members occupies no column"
  assertCheck (LeanDb.Entity.tableName Party.Guests == "party_guests") "stable association identity"
  let profile : Person := ⟨ada, email⟩
  match LeanDb.Entity.decode (α := Person) (LeanDb.Entity.encode profile) with
  | .error error => throw (IO.userError s!"profile decode: {error}")
  | .ok value => assertCheck (value.name == ada && value.email == email) "original type reconstruction"
  let unique : LeanDb.Unique Person := .byEmail
  let metadata := LeanDb.Unique.metadata unique
  assertCheck (metadata.columns == #["email"]) "portable unique native metadata"
  assertCheck (metadata.identity == "uq_person_byEmail") "stable unique identity"
  let personStorage := LeanDb.Domain.HasEntityStorage.storage (s := S) (T := Person)
  assertCheck (personStorage.sourceUnique unique == "DomainStorageFixture.Person.byEmail")
    "typed native unique alternative retains the exact shared semantic identity"
  let report := LeanDb.Domain.emailPreflight
    [(1, "Ada@Example.test"), (2, " ada@example.test "), (3, "bad"), (4, "grace@example.test")]
  assertCheck (report.invalid.map Prod.fst == [3]) "canonical migration invalid IDs"
  assertCheck (report.conflicts.map (·.rows) == [[1, 2]]) "canonical migration all colliding rows"
  let .ok title := Title.parse "A party" | throw (IO.userError "title parse")
  let .ok date := Instant.ofEpochSeconds 1000 | throw (IO.userError "date parse")
  let .ok description := Text.parse "" | throw (IO.userError "description parse")
  assertCheck ((LeanDb.Entity.check Party
    ⟨otherScopeRef, title, date, description, .public, {}⟩).toOption.isNone)
    "original Party cannot acquire Checked evidence for another storage scope"
  let nonce ← IO.monoNanosNow
  let path : System.FilePath := s!"/tmp/leandb-domain-bridge-{nonce}.sqlite"
  match ← LeanDb.withDb path (LeanDb.IsSchema.specs S) do
    let stored ← LeanDb.insert Person profile
    let .ok checked := LeanDb.Entity.check Person ⟨ada, email2⟩
      | throw (LeanDb.DbError.invariant "person" "checked shared scalar")
    match ← LeanDb.Txn.run (s := S) (ε := String) (do
      match ← LeanDb.Txn.insert Person checked with
      | .error (.duplicate index holder) => return (LeanDb.Unique.metadata index |>.identity, holder.toInt64)
      | .error (.missingRef fk) => nomatch fk
      | .ok _ => LeanDb.Txn.throw "canonical duplicate incorrectly inserted") with
    | .ok (.ok (identity, holder)) =>
        unless identity == "uq_person_byEmail" && holder == stored.id.toInt64 do
          throw (.sqlite "wrong native unique failure payload")
    | _ => throw (.sqlite "native canonical signup collision")
    let .ok hostRef := LeanDb.Domain.idToRef stored.id | throw (.sqlite "stored profile ref")
    let party ← LeanDb.insert Party ⟨hostRef, title, date, description, .public, {}⟩
    match ← LeanDb.Txn.run (s := S) (ε := String) (do
      let some current ← LeanDb.Txn.get Party party.id | LeanDb.Txn.throw "missing"
      (LeanDb.Txn.includeMember (Party.guestsRelation.bind current) stored.id).orAbort
        (fun _ => "missing membership reference")) with
    | .ok (.ok ()) => pure ()
    | _ => throw (.sqlite "bridge include")
    match ← LeanDb.Read.run (witnessedContains party.id stored.id) with
    | .ok true => pure ()
    | _ => throw (.sqlite "generated typed witness membership")
    match ← LeanDb.Read.run (s := S)
      (witnessedNames party.id) with
    | .ok names => unless names == [ada] do throw (.sqlite "bridge nonempty name projection")
    | .error fault => throw (.sqlite fault.message)
    let state ← LeanDb.DbState.load (s := S)
    unless state.checkWF do throw (.sqlite "bridge populated WF")
  with
  | .error error => throw (IO.userError s!"bridge SQLite: {error}")
  | .ok () => pure ()
  concurrentCanonical path ada
  match ← LeanDb.withDb path (LeanDb.IsSchema.specs S) do
    let _ ← LeanDb.untrackedSqlite fun db => db.exec "UPDATE person SET email = 'broken' WHERE id = 1"
    LeanDb.fetchAll Person
  with
  | .error (.decode table field _) =>
      assertCheck (table == "person" && field == "email") "typed corruption names original domain field"
  | .error error => throw (IO.userError s!"wrong corruption boundary: {error.message}")
  | .ok _ => throw (IO.userError "corrupted email reconstructed a valid domain record")
  IO.println "portable/native original-type storage checks passed"

end DomainStorageFixture

def main : IO Unit := DomainStorageFixture.main
