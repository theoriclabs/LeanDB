import TestsDddM2
open LeanDb TestsDddM2

-- Expected rejection: a migration can only fill a stored field of the entity.
migration% badField := Party.addField guestlist (fill := .everyone)
