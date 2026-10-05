import LeanDb.Typed.Members
open LeanDb
structure Person where
  name : String
  email : String
  deriving LeanDb.Entity
structure Party where
  title : String
  deriving LeanDb.Entity
members% Party.guests : Person
schema% S := Person, Party
#check Party.Guests
#check Party.guestsRelation
#synth IsSchema.Has S Party.Guests
#eval (IsSchema.specs S).map (fun s => (s.name, s.columns.map (fun c => (c.name, c.fkTable, c.cascade)), s.indexes))
