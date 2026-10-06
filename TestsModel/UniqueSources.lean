import LeanDb.Native

namespace UniqueSourcesFixture
open LeanDb.Model

structure Profile where
  email : Email
  deriving Entity

constraint Profile.primary : unique email
constraint Profile.alternate : unique email
native_schema% S := Profile

def run : IO Unit := do
  IO.FS.createDirAll ".lake/ddd-m2-scratch"
  let storage := LeanDb.Native.HasEntityStorage.storage (s := S) (T := Profile)
  unless storage.sourceUnique Profile.Unique.primary == "UniqueSourcesFixture.Profile.primary" &&
      storage.sourceUnique Profile.Unique.alternate == "UniqueSourcesFixture.Profile.alternate" do
    throw (IO.userError "semantic unique identities conflated equal column sets")
  unless (LeanDb.Unique.metadata (α := Profile) Profile.Unique.primary).identity == "uq_profile_primary" &&
      (LeanDb.Unique.metadata (α := Profile) Profile.Unique.alternate).identity == "uq_profile_alternate" do
    throw (IO.userError "physical unique identities conflated equal column sets")
  let .ok email := Email.parse "Ada@Example.test" | throw (IO.userError "email")
  let .ok equivalent := Email.parse " ada@example.test " | throw (IO.userError "equivalent email")
  let nonce ← IO.monoNanosNow
  match ← LeanDb.withDb s!".lake/ddd-m2-scratch/leandb-unique-sources-{nonce}.sqlite" (LeanDb.IsSchema.specs S) do
    let _ ← LeanDb.insert Profile ⟨email⟩
    let .ok checked := LeanDb.Entity.check Profile ⟨equivalent⟩ | throw (.sqlite "checked email")
    let program : {Scope : Type} → LeanDb.Txn Scope S String String := do
      match ← LeanDb.Txn.insert Profile checked with
      | .error (.duplicate index _) => return storage.sourceUnique index
      | .error (.missingRef fk) => nomatch fk
      | .ok _ => LeanDb.Txn.throw "canonical duplicate accepted"
    let before ← LeanDb.DbState.load (s := S)
    let expected := LeanDb.Txn.denote (program (Scope := Unit)) before
    match ← LeanDb.Txn.run program with
    | .ok (.ok source) =>
      unless ["UniqueSourcesFixture.Profile.primary", "UniqueSourcesFixture.Profile.alternate"].contains source &&
          expected.1 == .ok source do
        throw (.sqlite "actual native collision did not map to its exact semantic alternative")
    | _ => throw (.sqlite "unique source runtime failed")
    let after ← LeanDb.DbState.load (s := S)
    unless before.checkWF && after.checkWF &&
        (before.get (α := Profile)).next == (after.get (α := Profile)).next &&
        ((after.get (α := Profile)).rows.map fun row => (row.id, row.val.email.value)) ==
          ((expected.2.get (α := Profile)).rows.map fun row => (row.id, row.val.email.value)) &&
        (after.get (α := Profile)).rows.length == 1 do
      throw (.sqlite "duplicate changed original profile table/counter")
  with
  | .error error => throw (IO.userError error.message)
  | .ok () => IO.println "typed physical/semantic unique identity checks passed"

end UniqueSourcesFixture
