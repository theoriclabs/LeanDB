import TestsDddM2
open LeanDb TestsDddM2

-- Expected rejection: the post's `exportGuests`, written in another module,
-- forgets the visibility check. `Party.guests` still wants the proof.
def exportGuests (row : Valid Party) (role : Role) : Read S (List String) :=
  Party.guests row role
