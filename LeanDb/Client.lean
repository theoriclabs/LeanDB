import LeanDb.Cli

namespace LeanDb

/-! # A typed client for a served base

A project that imports a base package has its types and its query defs;
against a *local* instance it runs them in-process (`Base.withInstance`).
Against a *served* base it needs the wire: `Client` is a small transport
record. Its built-in constructor speaks JSON-lines to a base process
(`<base> serve`), and optional packages can supply HTTP or another transport.
`client% f` turns a query
def's signature into a stub — arguments rendered through `CliRender`,
the result decoded through `QueryIn` — so the call site is typed exactly
as the local one. The handshake compares fingerprints: a client compiled
against another version of the schema is refused before it asks. -/

open Lean (Json)

/-- How a typed argument renders for the wire (the inverse of `CliArg`).
    Closed enums render by variant name for free; bases add instances for
    their newtypes. -/
class CliRender (α : Type) where
  render : α → String

instance : CliRender Nat := ⟨toString⟩
instance : CliRender Int64 := ⟨toString⟩
instance : CliRender String := ⟨id⟩
instance : CliRender (Id α) := ⟨fun i => toString i.toInt64⟩
instance [ClosedEnum α] : CliRender α := ⟨ClosedEnum.encodeName⟩

/-- How a query result decodes from its JSON (the inverse of `QueryOut`). -/
class QueryIn (α : Type) where
  ofJson : Json → Except String α

/-- `Stored α` from row JSON: `id` plus the entity's fields. -/
def storedOfJson (α : Type) [Entity α] (j : Json) : Except String (Stored α) := do
  let id ← (j.getObjValAs? Int "id").mapError fun _ => s!"{Entity.tableName α}: row JSON without an id"
  let fields := match j with
    | .obj kvs => Json.mkObj (kvs.toList.filter (·.1 != "id"))
    | other => other
  let a ← (rowOfJson α fields).mapError (·.message)
  return ⟨⟨Int64.ofInt id⟩, a⟩

instance [Entity α] : QueryIn (Stored α) := ⟨storedOfJson α⟩
instance [QueryIn α] [QueryIn β] : QueryIn (α × β) := ⟨fun j => do
  match j with
  | .arr #[a, b] => return (← QueryIn.ofJson a, ← QueryIn.ofJson b)
  | other => throw s!"expected a pair, got {other.compress}"⟩
instance [QueryIn α] : QueryIn (Array α) := ⟨fun j => do
  match j with
  | .arr xs => xs.mapM QueryIn.ofJson
  | other => throw s!"expected an array, got {other.compress}"⟩
instance [QueryIn α] : QueryIn (List α) := ⟨fun j => (·.toList) <$> (QueryIn.ofJson j : Except String (Array α))⟩
instance [QueryIn α] : QueryIn (Option α) := ⟨fun j =>
  match j with
  | .null => pure none
  | other => some <$> QueryIn.ofJson other⟩
instance : QueryIn Nat := ⟨fun j => (j.getNat?).mapError fun _ => s!"expected a natural number, got {j.compress}"⟩
instance : QueryIn String := ⟨fun j => (j.getStr?).mapError fun _ => s!"expected a string, got {j.compress}"⟩
instance : QueryIn Bool := ⟨fun j => (j.getBool?).mapError fun _ => s!"expected a boolean, got {j.compress}"⟩
instance : QueryIn Unit := ⟨fun _ => pure ()⟩
instance : QueryIn Json := ⟨pure⟩

/-- A typed error back from the wire, by its code. -/
def DbError.ofJson (j : Json) : DbError :=
  let msg := (j.getObjValAs? String "message").toOption.getD j.compress
  match (j.getObjValAs? String "code").toOption with
  | some "decode" => .decode "remote" "result" msg
  | some "not_found" => .notFound "remote" 0
  | some "stale" => .stale "remote" 0
  | some "restricted" => .restricted "remote" 0
  | some "missing_ref" => .missingRef "remote"
  | some "duplicate" => .duplicate "remote" msg
  | some "schema_mismatch" => .schemaMismatch "" msg
  | some "schema" => .schemaInvalid msg
  | some "enum_drift" => .enumDrift "remote" "" msg
  | some "migrate" => .migrate msg
  | some "unknown_lineage" => .unknownLineage msg []
  | some "transport" => .transport msg
  | _ => .sqlite msg

/-- A connection to a served base. Transports implement one JSON argv request
    and cleanup; typed stubs and result decoding are transport-independent. -/
structure Client where
  rpc : List String → IO (Except DbError Json)
  fingerprint : String
  close : IO Unit

abbrev ClientM := ReaderT Client (ExceptT DbError IO)

def ClientM.run (c : Client) (act : ClientM α) : IO (Except DbError α) := (act c).run

/-- Map one line read from the served base to a response. The protocol
    has no request ids (issue #62): one stray child-stdout line shifts
    every later response onto the wrong request, so anything that is not
    a JSON object line — or a line past the read cap — is desync,
    a broken transport, never a silent mis-association. -/
def Client.processLine (raw : Cli.StdLine) : Except String Json :=
  match raw with
  | .eof => .error "the served base closed the connection"
  | .tooLong =>
      .error s!"the served base sent a line over the {Cli.defaultMaxLineBytes}-byte cap; the protocol is desynced"
  | .line out =>
      match Json.parse out.trimAscii.toString with
      | .ok j@(.obj _) => .ok j
      | .ok j => .error s!"the served base sent a non-object line (protocol desync): {j.compress}"
      | .error m => .error s!"unparseable response from the served base: {m}"

/-- One line from a handle, with a byte cap. `IO.FS.Handle.read n` is
    `fread`: it blocks until `n` bytes or EOF, so a chunked reader
    (`Cli.LineReader`) wedges on a live pipe that has emitted less than a
    chunk — a child answering a 34-byte JSON line and waiting would wedge
    the host forever. Single-byte reads — what `getLine` does under the
    hood — never wedge, and the cap bounds the buffer `getLine` would
    grow without limit (issue #62: a newline-less child banner OOM'd the
    host). Past the cap it returns `tooLong` without draining; the caller
    kills the child, so no resync is needed. -/
private partial def nextLineLoop (h : IO.FS.Handle) (cap : Nat) (acc : ByteArray) :
    IO Cli.StdLine := do
  if acc.size > cap then return .tooLong
  let chunk ← h.read 1
  if chunk.size == 0 then
    if acc.isEmpty then return .eof
    return .line (String.fromUTF8? acc |>.getD "")
  match chunk[0]! with
  | 10 => return .line (String.fromUTF8? acc |>.getD "")
  | b => nextLineLoop h cap (acc.push b)

/-- One capped protocol line from a child's stdout. -/
def Client.nextLine (h : IO.FS.Handle) (cap : Nat := Cli.defaultMaxLineBytes) :
    IO Cli.StdLine :=
  nextLineLoop h cap ByteArray.empty

-- No handshake deadline yet (issue #62, facet 2, open): the read below
-- blocks until the child writes or closes.
/-- One rpc over a spawned base's pipes: the request is one JSON argv
    line, the response one capped line (an uncapped `getLine` OOM'd the
    host on a newline-less child banner, issue #62). A refused line kills
    the child: with no ids, a desynced stream cannot be trusted again. -/
private def processRpc
    (child : IO.Process.Child { stdin := .piped, stdout := .piped, stderr := .inherit })
    (argv : List String) : IO (Except DbError Json) := do
  try
    let line := (Json.arr (argv.map Json.str).toArray).compress
    child.stdin.putStrLn line
    child.stdin.flush
    let raw ← Client.nextLine child.stdout
    match Client.processLine raw with
    | .ok j => return .ok j
    | .error m =>
        unless raw matches .eof do
          try child.kill catch _ => pure ()
        return .error (.transport m)
  catch e =>
    return .error (.transport (toString e))

/-- Wrap an already-spawned `<base> serve` process. Most callers should use
    `Client.connect`; the host uses this before learning the child's fingerprint. -/
def Client.ofProcess
    (child : IO.Process.Child { stdin := .piped, stdout := .piped, stderr := .inherit })
    (fingerprint : String := "") : Client := {
  rpc := processRpc child
  fingerprint
  close := do
    try child.kill catch _ => pure ()
    try discard <| child.wait catch _ => pure () }

/-- Spawn `<exe> serve` (plus `args`, e.g. `--db path`) and shake hands:
    the served schema must be the one this client was compiled against. -/
def Client.connect (exe : System.FilePath) (fingerprint : String) (args : List String := []) :
    IO (Except DbError Client) := do
  let cfg : IO.Process.SpawnArgs := {
    cmd := exe.toString
    args := (args ++ ["serve"]).toArray
    stdin := .piped
    stdout := .piped
    stderr := .inherit }
  try
    let child ← IO.Process.spawn cfg
    let c := Client.ofProcess child fingerprint
    match ← c.rpc ["version"] with
    | .error e => c.close; return .error e
    | .ok v =>
        match (v.getObjValAs? String "code_fingerprint").toOption with
        | some fp =>
            if fp != fingerprint then
              c.close
              return .error (.schemaMismatch fingerprint fp)
            return .ok c
        | none =>
            c.close
            return .error (.transport s!"the served base did not answer version: {v.compress}")
  catch e =>
    return .error (.transport (toString e))

/-- Call a registered query by name; the result is the query's JSON. -/
def Client.call (name : String) (args : List String) : ClientM Json := fun c => ExceptT.mk do
  match ← c.rpc (["query", name] ++ args) with
  | .error e => return .error e
  | .ok j =>
      if (j.getObjValAs? Bool "ok").toOption == some true then
        return .ok ((j.getObjVal? "result").toOption.getD Json.null)
      else
        return .error (DbError.ofJson j)

/-- Decode a typed result. -/
def ClientM.decode (α : Type) [QueryIn α] (j : Json) : ClientM α := fun _ => ExceptT.mk <|
  pure ((QueryIn.ofJson j : Except String α).mapError fun m => .decode "remote" "result" m)

/-- Any argv through the client (rows, insert, migrate status, …). -/
def Client.argv (argv : List String) : ClientM Json := fun c => ExceptT.mk do
  match ← c.rpc argv with
  | .error e => return .error e
  | .ok j =>
      if (j.getObjValAs? Bool "ok").toOption == some true then return .ok j
      else return .error (DbError.ofJson j)

end LeanDb

namespace LeanDb.Cli
open Lean Elab Term Meta

/-- `client% slaBreached` turns `def slaBreached (now : Timestamp) : DbM ρ`
    into `fun now => … : ClientM ρ`: each argument renders through its
    type's `CliRender`, the call goes over the wire under the def's name,
    the result decodes through `QueryIn ρ`. The stub's type is the local
    def's with `DbM` replaced by `ClientM`, so a wrong argument or a
    result the project cannot decode is a compile error. -/
elab "client% " id:ident : term => do
  let name ← realizeGlobalConstNoOverloadWithInfo id
  let info ← getConstInfo name
  let (binderNames, binderTys, retTy) ← forallTelescope info.type fun xs body => do
    unless body.isAppOf ``LeanDb.DbM do
      throwError "client%: {name} must return in DbM, found {body}"
    let mut names : Array Name := #[]
    let mut tys : Array Term := #[]
    for x in xs do
      let decl ← x.fvarId!.getDecl
      unless decl.binderInfo == .default do
        throwError "client%: {name} has non-explicit binder '{decl.userName}'"
      names := names.push decl.userName
      tys := tys.push (← PrettyPrinter.delab (← instantiateMVars decl.type))
    let ret ← PrettyPrinter.delab (← instantiateMVars (body.getArg! 0))
    return (names, tys, ret)
  let nameLit : Term := quote name.getString!
  let idents := binderNames.map fun n => mkIdent n
  let rendered ← (idents.zip binderTys).mapM fun (x, ty) =>
    `(LeanDb.CliRender.render ($x : $ty))
  let args : Term ← `([$rendered,*])
  let body : Term ← `((LeanDb.Client.call $nameLit $args >>= LeanDb.ClientM.decode $retTy : LeanDb.ClientM $retTy))
  let binders ← (idents.zip binderTys).mapM fun (x, ty) => `(Lean.Parser.Term.funBinder| ($x : $ty))
  let stx ← if binders.isEmpty then pure body else `(fun $binders* => $body)
  elabTerm stx none

end LeanDb.Cli
