/-! Portable domain types with no LeanDB import (LDB-10).
    Storage codecs are derived post-hoc in the test module. -/

inductive PortableRole where
  | admin | user
  deriving Repr, DecidableEq

structure PortableReply where
  body : String
  deriving Repr

/-- LDB-12: a validated nested type — two proof fields over one data
    field. A derive cannot walk it (the proofs' types depend on `s`), so
    the native package stores it through `s` with `DbJson.via`. -/
structure ProofText where
  s : String
  nonempty : 0 < s.length
  noBreak : s.contains '\n' = false

def ProofText.make (s : String) : Except String ProofText :=
  if h : 0 < s.length then
    if hb : s.contains '\n' = false then .ok ⟨s, h, hb⟩
    else .error "text: contains a line break"
  else .error "text: empty"

/-- A second validation over a wider data representation: changing the
    data field's type must change the shape and the fingerprint. -/
structure ProofTextWide where
  s : String
  lang : String
  nonempty : 0 < s.length

def ProofTextWide.make (s lang : String) : Except String ProofTextWide :=
  if h : 0 < s.length then .ok ⟨s, lang, h⟩ else .error "wide text: empty"

/-- The portable model the proof-field type nests into, three levels down
    (`ProofDoc → ProofParagraph → ProofRun → ProofText`). -/
structure ProofRun where
  text : ProofText
  bold : Bool := false

structure ProofParagraph where
  runs : List ProofRun

structure ProofDoc where
  title : ProofText
  paras : List ProofParagraph := []

/-- Same tree over the wider data representation. -/
structure ProofWideDoc where
  title : ProofTextWide
  paras : List ProofParagraph := []
