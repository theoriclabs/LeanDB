import LeanDbDomain

namespace DomainAccessFixture
open LeanApp.Domain

@[entity] structure Person where
  name : Name
  email : Email

@[entity] structure Party where
  host : Ref Person
  title : Title
  guests : Members Person := {}

native_schema% S := Person, Party

private def sameTable {T} [LeanDb.Entity T] [LeanDb.IsSchema.Has S T]
    (a b : LeanDb.DbState S) : Bool :=
  let left := a.get (α := T)
  let right := b.get (α := T)
  left.next == right.next && left.rows.length == right.rows.length &&
    (left.rows.zip right.rows).all (fun (x, y) =>
      x.id == y.id && LeanDb.Entity.encode x.val == LeanDb.Entity.encode y.val)

private def same (a b : LeanDb.DbState S) : Bool :=
  sameTable (T := Person) a b && sameTable (T := Party) a b &&
    sameTable (T := Party.Guests) a b

def main : IO Unit := do
  let .ok name := Name.parse "Ada" | throw (IO.userError "name")
  let .ok email := Email.parse "ada@example.test" | throw (IO.userError "email")
  let .ok title := Title.parse "Gathering" | throw (IO.userError "title")
  let entity := LeanDb.Domain.HasEntityStorage.storage (s := S) (T := Person)
  let members := LeanDb.Domain.HasMemberStorage.storage (s := S) (Parent := Party)
    (field := "guests") (Target := Person)
  let column := LeanDb.Domain.HasFieldStorage.storage (s := S) (T := Person)
    (field := "name") (Value := Name)
  let .ok wrongScope := Ref.parse (T := Person) "1" "other"
    | throw (IO.userError "scope")
  unless (entity.find (Scope := Unit) wrongScope).toOption.isNone do
    throw (IO.userError "native find collapsed identity scopes")
  let nonce ← IO.monoNanosNow
  match ← LeanDb.withDb s!"/tmp/leandb-domain-access-{nonce}.sqlite" (LeanDb.IsSchema.specs S) do
    let person ← LeanDb.insert Person ⟨name, email⟩
    let .ok personRef := LeanDb.Domain.idToRef person.id | throw (.sqlite "person ref")
    let party ← LeanDb.insert Party ⟨personRef, title, {}⟩
    let .ok partyRef := LeanDb.Domain.idToRef party.id | throw (.sqlite "party ref")
    let .ok lookupPlan := entity.find (Scope := Unit) personRef | throw (.sqlite "find plan")
    match ← LeanDb.Read.run lookupPlan with
    | .ok (some live) =>
      unless live.id == personRef && live.value.name == name && live.value.email == email do
        throw (.sqlite "find did not reconstruct the original domain record")
    | _ => throw (.sqlite "live find failed")
    let .ok absent := Ref.parse (T := Person) "999" | throw (.sqlite "missing ref")
    let .ok findMissing := entity.find (Scope := Unit) absent | throw (.sqlite "missing find plan")
    match ← LeanDb.Read.run findMissing with
    | .ok none => pure ()
    | _ => throw (.sqlite "missing find invented a row")
    let before ← LeanDb.DbState.load (s := S)
    let includeProgram : {Scope : Type} → LeanDb.Txn Scope S String Unit := do
      -- The authenticated ID supplies the target. No input person ID exists.
      let actor := Trusted.signedIn (Trusted.row personRef person.val)
      let .ok includePlan := members.includeActor partyRef actor "missingLiveParty"
        | LeanDb.Txn.throw "include plan failed"
      includePlan.orAbort (fun _ => "include reference failure")
      includePlan.orAbort (fun _ => "retry reference failure")
    let expected := LeanDb.Txn.denote (includeProgram (Scope := Unit)) before
    match ← LeanDb.Txn.run includeProgram with
    | .ok (.ok ()) => pure ()
    | _ => throw (.sqlite "authenticated witnessed include failed")
    let after ← LeanDb.DbState.load (s := S)
    unless before.checkWF && after.checkWF &&
        (after.get (α := Party.Guests)).rows.length == 1 &&
        expected.1 == .ok () && same expected.2 after do
      throw (.sqlite "include/retry did not produce one lawful pair")
    let .ok contains := members.contains partyRef personRef | throw (.sqlite "contains plan")
    match ← LeanDb.Read.run contains with
    | .ok true => pure ()
    | _ => throw (.sqlite "witnessed indexed contains")
    let .ok projection := members.project column partyRef | throw (.sqlite "column plan")
    match ← LeanDb.Read.run projection with
    | .ok names =>
      unless names == [name] && names == LeanDb.Read.denote projection after do
        throw (.sqlite "names-only projection/denotation")
    | _ => throw (.sqlite "column projection failed")
    let .ok missingParty := Ref.parse (T := Party) "999" | throw (.sqlite "missing party ref")
    match ← LeanDb.Txn.run (s := S) (ε := String) (do
      let actor := Trusted.signedIn (Trusted.row personRef person.val)
      let .ok includePlan := members.includeActor missingParty actor "missingLiveParty"
        | LeanDb.Txn.throw "missing include plan failed"
      includePlan.orAbort (fun _ => "unexpected foreign key failure")) with
    | .ok (.error "missingLiveParty") => pure ()
    | _ => throw (.sqlite "include trusted a missing parent")
    unless same after (← LeanDb.DbState.load (s := S)) do
      throw (.sqlite "missing live parent changed tables/counters")
    unless (members.contains partyRef wrongScope).toOption.isNone do
      throw (.sqlite "member hook collapsed target scopes")
  with
  | .error error => throw (IO.userError error.message)
  | .ok () => IO.println "native witnessed lookup/contains/projection/authenticated include checks passed"

end DomainAccessFixture

def main : IO Unit := DomainAccessFixture.main
