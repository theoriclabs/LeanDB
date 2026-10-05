import PostPart1
import LeanDbDomain

/- Expected rejection: lookup evidence exists only for the DECLARED constraint's
key constant. A hand-built key with the same identity, fields and projection
is not `Rsvp.onePerGuest.key`, so it cannot probe the native index. -/
open LeanApp.Domain

native_schema% PostSchema := Person, Party, Rsvp

def forgedKey : UniqueKey Rsvp (Ref Party × Ref Person) :=
  { identity := "Rsvp.onePerGuest", fields := ["party", "guest"],
    key := fun r => (r.party, r.guest), equal := fun a b => a == b }

#synth HasUniqueResource (LeanDb.Domain.storageResources PostSchema) Rsvp (Ref Party × Ref Person)
  HasEntityResource.witness forgedKey
