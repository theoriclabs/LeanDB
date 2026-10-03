import TestsDddM2
open LeanDb TestsDddM2

-- Expected rejection: a migration's fill has the field's type.
migration% badFill := Party.addField guestList (fill := "everyone")
