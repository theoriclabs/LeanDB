import LeanDb

/-! LDB-15: `append` — grow a child list against the value that was read.

A stale writer whose parent columns match but whose list moved on is
refused with `.stale`, in one connection and across two; the stored rows
are never rewritten; a value that is not an extension is `.notAppend`. -/

namespace TestsLdb15

open LeanDb

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw <| IO.userError s!"FAIL: {message}"

private def expectOk (r : Except DbError α) (context : String) : IO α :=
  match r with
  | .ok a => pure a
  | .error e => throw <| IO.userError s!"FAIL: {context}: {e}"

private def expectCode (r : Except DbError α) (code context : String) : IO Unit :=
  match r with
  | .ok _ => throw <| IO.userError s!"FAIL: {context}: expected {code}, got success"
  | .error e => check (e.code == code) s!"{context}: expected {code}, got {e}"

structure Entry where
  text : String
  deriving Repr, BEq, LeanDb.Inline

structure Journal where
  title : String
  entries : List Entry
  deriving Repr, LeanDb.Entity

private def specs : List TableSpec := Entity.specs Journal

private def dbPath : System.FilePath := ".lake" / "leandb_test_ldb15.sqlite"

private def fresh (p : System.FilePath) : IO Unit := do
  if ← p.pathExists then IO.FS.removeFile p
  for suffix in ["-wal", "-shm"] do
    let side : System.FilePath := p.toString ++ suffix
    if ← side.pathExists then IO.FS.removeFile side

private def expectSome (o : Option α) (context : String) : IO α :=
  match o with
  | some a => pure a
  | none => throw <| IO.userError s!"FAIL: {context}: no row"

private def texts (s : Stored Journal) : List String := s.val.entries.map (·.text)

private def grow (s : Stored Journal) (t : String) : Journal :=
  { s.val with entries := s.val.entries ++ [⟨t⟩] }

/-- The child rows' own ids, in position order: `update` would renumber
    them all, `append` leaves them. -/
private def childIds (conn : Conn) : IO (Array Int64) := do
  let stmt ← conn.raw.prepare "SELECT id FROM \"journal_entries\" ORDER BY position"
  let mut out := #[]
  repeat
    if ← stmt.step then out := out.push (← stmt.columnInt64 0) else break
  return out

private def testAppend : IO Unit := do
  fresh dbPath
  let conn ← expectOk (← openDb dbPath specs) "open"
  let s0 ← expectOk (← DbM.run conn (insert Journal ⟨"game", [⟨"e4"⟩]⟩)) "insert"
  let before ← childIds conn
  let s1 ← expectOk (← DbM.run conn (append s0 (grow s0 "e5"))) "append"
  check (texts s1 == ["e4", "e5"]) "append returns the grown value"
  let back ← expectOk (← DbM.run conn (get s0.id)) "read back"
  check ((back.map texts) == some ["e4", "e5"]) s!"stored list grew: {back.map texts}"
  let after ← childIds conn
  check (after.extract 0 before.size == before) s!"stored child rows kept their ids: {before} → {after}"
  check (after.size == 2) "one child row added"
  -- a second append from the fresh value
  let s2 ← expectOk (← DbM.run conn (append s1 (grow s1 "Nf3"))) "append again"
  check (texts s2 == ["e4", "e5", "Nf3"]) "second append"
  -- appending nothing is a no-op that still checks staleness
  discard <| expectOk (← DbM.run conn (append s2 s2.val)) "empty append"

/-- Two writers read the same value; identical parent columns, divergent
    lists. The first commits; the second is `.stale`; nothing is lost. -/
private def testStaleSameConnection : IO Unit := do
  fresh dbPath
  let conn ← expectOk (← openDb dbPath specs) "open"
  let s0 ← expectOk (← DbM.run conn (insert Journal ⟨"game", [⟨"e4"⟩]⟩)) "insert"
  discard <| expectOk (← DbM.run conn (append s0 (grow s0 "e5"))) "first writer"
  expectCode (← DbM.run conn (append s0 (grow s0 "c5"))) "stale" "second writer from the stale read"
  let back ← expectOk (← DbM.run conn (get s0.id)) "read back"
  check ((back.map texts) == some ["e4", "e5"]) s!"first writer's row survives: {back.map texts}"
  -- the parent's columns move with an append
  let cur ← expectSome (← expectOk (← DbM.run conn (get s0.id)) "cur") "cur"
  let moved ← expectOk (← DbM.run conn (append cur { grow cur "Nf3" with title := "Sicilian?" })) "append and retitle"
  check (moved.val.title == "Sicilian?" && texts moved == ["e4", "e5", "Nf3"]) "parent and list both moved"
  -- a parent column moved on since the read: also stale
  let cur ← expectSome (← expectOk (← DbM.run conn (get s0.id)) "cur") "cur"
  discard <| expectOk (← DbM.run conn (update cur { cur.val with title := "renamed" })) "rename"
  expectCode (← DbM.run conn (append cur (grow cur "Nc3"))) "stale" "parent changed since the read"
  -- the row is gone
  expectCode (← DbM.run conn (append { cur with id := ⟨9999⟩ } (grow cur "Nf3"))) "not_found" "no such row"

/-- The same race across two connections. -/
private def testStaleTwoConnections : IO Unit := do
  fresh dbPath
  let c1 ← expectOk (← openDb dbPath specs) "conn1"
  let c2 ← expectOk (← openDb dbPath specs) "conn2"
  let s0 ← expectOk (← DbM.run c1 (insert Journal ⟨"game", [⟨"e4"⟩]⟩)) "insert"
  let seen ← expectSome (← expectOk (← DbM.run c2 (get s0.id)) "conn2 reads") "conn2 reads"
  discard <| expectOk (← DbM.run c1 (append s0 (grow s0 "e5"))) "conn1 appends"
  expectCode (← DbM.run c2 (append seen (grow seen "c5"))) "stale" "conn2 appends from its stale read"
  let back ← expectOk (← DbM.run c2 (get s0.id)) "read back"
  check ((back.map texts) == some ["e4", "e5"]) s!"one linear successor: {back.map texts}"

/-- A list that does not continue the stored one is an `update`. -/
private def testNotAppend : IO Unit := do
  fresh dbPath
  let conn ← expectOk (← openDb dbPath specs) "open"
  let s0 ← expectOk (← DbM.run conn (insert Journal ⟨"game", [⟨"e4"⟩, ⟨"e5"⟩]⟩)) "insert"
  expectCode (← DbM.run conn (append s0 { s0.val with entries := [⟨"d4"⟩, ⟨"e5"⟩, ⟨"c4"⟩] }))
    "not_append" "an existing entry changed"
  expectCode (← DbM.run conn (append s0 { s0.val with entries := [⟨"e4"⟩] })) "not_append"
    "the list shrank"
  let back ← expectOk (← DbM.run conn (get s0.id)) "read back"
  check ((back.map texts) == some ["e4", "e5"]) "refusals wrote nothing"

def run : IO Unit := do
  testAppend
  testStaleSameConnection
  testStaleTwoConnections
  testNotAppend

end TestsLdb15
