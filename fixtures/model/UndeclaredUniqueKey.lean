/- Lookup evidence exists only for the DECLARED constraint's key constant. A hand-built key
   with the same identity, fields and projection is not `Rsvp.onePerGuest.key`, so it cannot
   probe the native index. -/
import TestsModel.Post
import LeanDb.Native
open LeanDb.Model

native_schema% PostSchema := Person, Party, Rsvp

def forgedKey : UniqueKey Rsvp (Ref Party × Ref Person) :=
  { identity := "Rsvp.onePerGuest", fields := ["party", "guest"],
    key := fun r => (r.party, r.guest), equal := fun a b => a == b }

#synth HasUniqueResource (LeanDb.Native.storageResources PostSchema) Rsvp (Ref Party × Ref Person)
  HasEntityResource.witness forgedKey
