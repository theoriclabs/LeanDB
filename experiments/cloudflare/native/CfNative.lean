import LeanDb

namespace CfNative
open LeanDb Lean

structure Counter where
  tenant : String
  key : String
  value : Int64
  deriving Repr, LeanDb.Entity
unique% Counter.tenantKey := (tenant, key)
typed% Counter

/-- The envelope is the original argument string, not reserialized JSON. -/
structure Applied where
  seq : Int64
  envelope : String
  result : String
  deriving Repr, LeanDb.Entity
unique% Applied.sequence := seq
typed% Applied

private def failure (code : String) : Json :=
  Json.mkObj [("ok", toJson false), ("code", toJson code)]

private def rejected (seq : Int64) (code : String) : Json :=
  Json.mkObj [("ok", toJson false), ("seq", toJson seq.toInt), ("code", toJson code)]

private def accepted (seq value : Int64) : Json :=
  Json.mkObj [("ok", toJson true), ("seq", toJson seq.toInt), ("value", toJson value.toInt)]

/-- Shared policy for both mutations and snapshots. The gateway supplies actor. -/
private def allowed (actor tenant : String) : Bool :=
  (actor == "alice" && tenant == "alpha") || (actor == "bob" && tenant == "beta")

private def checkedInt64 (i : Int) : Except String Int64 :=
  if i < Int64.minValue.toInt || i > Int64.maxValue.toInt then .error "invalid"
  else .ok (Int64.ofInt i)

private def integer (j : Json) (key : String) : Except String Int64 := do
  let i ← (j.getObjValAs? Int key).mapError (fun _ => "invalid")
  checkedInt64 i

private structure Command where
  actor : String
  kind : String
  tenant : String
  key : String
  amount : Int64

private def parseCommand (j : Json) : Except String Command := do
  let actor ← (j.getObjValAs? String "actor").mapError (fun _ => "invalid")
  let _ ← (j.getObjValAs? String "requestId").mapError (fun _ => "invalid")
  let c ← (j.getObjVal? "command").mapError (fun _ => "invalid")
  let kind ← (c.getObjValAs? String "type").mapError (fun _ => "invalid")
  let tenant ← (c.getObjValAs? String "tenant").mapError (fun _ => "invalid")
  let key ← (c.getObjValAs? String "key").mapError (fun _ => "invalid")
  unless ["alice", "bob"].contains actor && ["alpha", "beta"].contains tenant &&
      ["create", "increment", "rollback"].contains kind do
    throw "invalid"
  -- Optional fields are optional across the union; each command needs its operand.
  -- If an unused numeric field is present, it must still be an integer.
  for field in ["value", "delta"] do
    if (c.getObjVal? field).isOk then discard <| integer c field
  let amount ← integer c (if kind == "create" then "value" else "delta")
  return { actor, kind, tenant, key, amount }

/-- Execute inside a savepoint. Domain aborts roll back before the caller writes
    Applied; unexpected engine errors propagate and never consume a sequence. -/
private def mutate (j : Json) : DbM (Tx String Int64) := do
  let .ok c := parseCommand j | return .abort "invalid"
  unless allowed c.actor c.tenant do return .abort "forbidden"
  if c.kind == "create" then
    try
      let row ← insert Counter { tenant := c.tenant, key := c.key, value := c.amount }
      return .commit row.val.value
    catch e =>
      match e with
      | .duplicate _ _ => return .abort "duplicate"
      | _ => throw e
  let some row := (← fetchAll Counter).find?
      (fun row => row.val.tenant == c.tenant && row.val.key == c.key) |
    return .abort "not_found"
  let .ok value := checkedInt64 (row.val.value.toInt + c.amount.toInt) |
    return .abort "invalid"
  discard <| update row { row.val with value }
  if c.kind == "rollback" then return .abort "rolled_back"
  return .commit value

/-- Sequence validation, successful mutation, and receipt share one write lock
    and commit. Nested transaction uses an actual SQLite SAVEPOINT. -/
def apply (raw : String) : DbM Json := do
  let .ok j := Json.parse raw | return rejected 0 "invalid"
  let .ok seq := integer j "seq" | return rejected 0 "invalid"
  if seq <= 0 then return rejected seq "invalid"
  withTransaction do
    let receipts ← fetchAll Applied
    if let some old := receipts.find? (·.val.seq == seq) then
      if old.val.envelope != raw then return rejected seq "sequence_conflict"
      -- Corrupt stored JSON is an engine failure, never a replacement receipt.
      return ← DbM.ofExcept ((Json.parse old.val.result).mapError
        (DbError.decode "applied" "result"))
    let lastSeq := receipts.foldl (fun n row => max n row.val.seq.toInt) (0 : Int)
    if seq.toInt != lastSeq + 1 then return rejected seq "sequence_gap"
    let outcome ← LeanDb.transaction (mutate j)
    let result := match outcome with
      | .ok value => accepted seq value
      | .error code => rejected seq code
    discard <| insert Applied { seq, envelope := raw, result := result.compress }
    return result

def snapshot (raw : String) : DbM Json := do
  let .ok j := Json.parse raw | return failure "invalid"
  let .ok actor := j.getObjValAs? String "actor" | return failure "invalid"
  let .ok tenant := j.getObjValAs? String "tenant" | return failure "invalid"
  unless allowed actor tenant do return failure "forbidden"
  let rows := ((← fetchAll Counter).filter (·.val.tenant == tenant)).qsort
    (fun a b => a.val.key < b.val.key)
  let items := rows.map fun row => Json.mkObj
    [("key", toJson row.val.key), ("value", toJson row.val.value.toInt)]
  let sum := rows.foldl (fun n row => n + row.val.value.toInt) (0 : Int)
  return Json.mkObj [("ok", toJson true), ("items", Json.arr items),
    ("sum", toJson sum), ("count", toJson rows.size)]

def status : DbM Json := do
  let lastSeq := (← fetchAll Applied).foldl (fun n row => max n row.val.seq.toInt) (0 : Int)
  return Json.mkObj [("ok", toJson true), ("lastSeq", toJson lastSeq),
    ("schemaVersion", toJson "cf-v1")]

private def oneArg (f : String → DbM Json) (args : List String) : DbM Json :=
  match args with
  | [raw] => f raw
  | _ => pure (failure "invalid")

/-- Keep schema discovery, but close generic row verbs that have no tenant actor.
    Only the named protocol queries may read or mutate these tables. -/
private def queryOnly (table : CliTable) : CliTable :=
  { table with
    insertJson := fun _ => throw (.readOnly "use the apply query")
    getJson := fun _ => throw (.readOnly "use the snapshot query")
    updateJson := fun _ _ => throw (.readOnly "use the apply query")
    deleteRow := fun _ => throw (.readOnly "use the apply query")
    rowsWhere := fun _ _ => throw (.readOnly "use the snapshot query") }

def base : Base := {
  name := "cf-native"
  -- CliTable.of erases the concrete Indexes instance; retain UNIQUE DDL here.
  tables := [
    queryOnly { CliTable.of Counter with specs := Entity.specs Counter },
    queryOnly { CliTable.of Applied with specs := Entity.specs Applied }]
  queries := [
    { name := "apply", run := fun args => Cli.okResult <$> (match args with
        | [raw] => apply raw
        | _ => pure (rejected 0 "invalid")) },
    { name := "snapshot", run := fun args => Cli.okResult <$> oneArg snapshot args },
    { name := "status", run := fun args => Cli.okResult <$> (match args with
        | [] => status
        | _ => pure (failure "invalid")) }]
}

end CfNative
