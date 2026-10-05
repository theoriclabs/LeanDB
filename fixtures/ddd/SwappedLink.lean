import TestsDddM2
open LeanDb TestsDddM2

-- Expected rejection: the SQL column and the getter the meaning reads must
-- be the same field. Here the parent column is `guest` but the getter reads
-- `party`.
def swapped : LinkRelation Party Person Rsvp where
  parentField := Rsvp.Field.guest
  targetField := Rsvp.Field.guest
  getParent := (·.party)
  getTarget := (·.guest)
  parentColumn := fun _ => rfl
  targetColumn := fun _ => rfl
