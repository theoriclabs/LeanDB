import LeanDb.Model

/- #141: compiling wireDefaults for an optional record default used to
   fail in Lean 4.33's IR checker with an unknown join point. Check both
   absent and present values, and a plain record default. -/

namespace DefaultFixture
open LeanDb.Model

structure IdempotencyKey where
  raw : String
  deriving Domain

instance : FieldType (Option IdempotencyKey) := ⟨.value, ⟨.none, false⟩⟩

structure Observation where
  launchKey : Option IdempotencyKey := none
  deriving Entity

structure Present where
  launchKey : Option IdempotencyKey := some ⟨"launch"⟩
  deriving Domain

structure Fallback where
  key : IdempotencyKey := ⟨"fallback"⟩
  deriving Entity

instance originalDefault : Inhabited IdempotencyKey := ⟨⟨"definition site"⟩⟩

structure DerivedLater where
  key : IdempotencyKey := default

section
local instance : Inhabited IdempotencyKey := ⟨⟨"derivation site"⟩⟩
deriving instance Entity for DerivedLater
end

#guard Observation.wireDefaults ==
  [("launchKey", Lean.Json.mkObj [("tag", .str "none")])]
#guard Present.wireDefaults ==
  [("launchKey", Lean.Json.mkObj [("tag", .str "some"),
    ("value", Lean.Json.mkObj [("raw", .str "launch")])])]
#guard Fallback.wireDefaults ==
  [("key", Lean.Json.mkObj [("raw", .str "fallback")])]
#guard DerivedLater.wireDefaults ==
  [("key", Lean.Json.mkObj [("raw", .str "definition site")])]

end DefaultFixture
