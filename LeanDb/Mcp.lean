import LeanDb.Cli

namespace LeanDb.Mcp

/-! # MCP over the handler

`<base> serve --mcp` speaks the Model Context Protocol (JSON-RPC 2.0 over
stdio, one message per line) with a tool list *derived* from the base:
one tool per table verb, one per registered query with its parameters
as the input schema (names and types from `query%`, closed worlds as
enums), plus schema/version/log/migrate status. Every call is one argv
through `Base.handle`, so an agent's surface is exactly the CLI's — it
picks from the list, it cannot invent a query. -/

open Lean (Json)

private def str (s : String) : Json := Json.str s

/-- JSON Schema for a parameter, from the type `query%` recorded. -/
private def paramSchema (ty : String) (enums : List (String × List String)) : Json :=
  match enums.lookup ty with
  | some vs => Json.mkObj [("type", str "string"), ("enum", Json.arr (vs.map str).toArray)]
  | none =>
      if ty == "Nat" || ty == "Int64" || ty.startsWith "Id " || ty.startsWith "Ref " then
        Json.mkObj [("type", str "integer")]
      else Json.mkObj [("type", str "string"), ("description", str s!"a {ty}")]

private def objectSchema (props : List (String × Json)) (required : List String) : Json :=
  Json.mkObj [("type", str "object"), ("properties", Json.mkObj props),
    ("required", Json.arr (required.map str).toArray)]

private def tool (name description : String) (input : Json) : Json :=
  Json.mkObj [("name", str name), ("description", str description), ("inputSchema", input)]

/-- Closed worlds the base's specs know, by column type name — used to
    offer enums for query parameters whose type name matches a table's
    closed-world column type. `query%` records the type name; a
    `ClosedEnum` type's variants are those of any column typed by it. -/
def enumsOf (b : Base) : List (String × List String) :=
  -- The specs carry variants per column, not per type; a parameter typed
  -- like a closed world is matched by the type's last name component
  -- against the column names' worlds when they agree. Best effort.
  []

/-- The tool list derived from the base. -/
def tools (b : Base) : Array Json := Id.run do
  let enums := enumsOf b
  let mut out : Array Json := #[
    tool "schema" s!"The {b.name} schema as JSON, derived from the types (closed worlds visible)."
      (objectSchema [] []),
    tool "version" "Code vs instance schema fingerprint, schema_version, in_sync." (objectSchema [] []),
    tool "log" "Recent query log entries: verb, plan, outcome, row count."
      (objectSchema [("limit", Json.mkObj [("type", str "integer")])] []),
    tool "migrate_status" "The pending schema migration: steps, destructiveness, changed columns, impacted queries."
      (objectSchema [] [])]
  if b.seed.isSome then
    out := out.push (tool "seed" "Load the base's seed data." (objectSchema [] []))
  for t in b.tables do
    out := out.push <| tool s!"rows_{t.name}"
      s!"Rows of {t.name} with conjunctive equality filters (col=value) and a limit."
      (objectSchema [("eq", Json.mkObj [("type", str "array"), ("items", Json.mkObj [("type", str "string")]),
          ("description", str "filters, each `column=value`")]),
        ("limit", Json.mkObj [("type", str "integer")])] [])
    out := out.push <| tool s!"get_{t.name}" s!"One row of {t.name} by id."
      (objectSchema [("id", Json.mkObj [("type", str "integer")])] ["id"])
    out := out.push <| tool s!"insert_{t.name}" s!"Insert a {t.name} row (decoded through the smart constructors; defaults fill omitted fields)."
      (objectSchema [("row", Json.mkObj [("type", str "object")])] ["row"])
    out := out.push <| tool s!"update_{t.name}" s!"Merge a partial row into {t.name} by id (re-validated, compare-and-swap)."
      (objectSchema [("id", Json.mkObj [("type", str "integer")]), ("row", Json.mkObj [("type", str "object")])] ["id", "row"])
    out := out.push <| tool s!"delete_{t.name}" s!"Delete a {t.name} row by id (refused while referenced)."
      (objectSchema [("id", Json.mkObj [("type", str "integer")])] ["id"])
  for q in b.queries do
    let props := q.params.map fun (n, ty) => (n, paramSchema ty enums)
    out := out.push <| tool s!"query_{q.name}"
      (s!"Registered query {q.name}" ++ (if q.params.isEmpty then "." else
        s!" ({String.intercalate ", " (q.params.map fun (n, ty) => s!"{n} : {ty}")})."))
      (objectSchema props (q.params.map (·.1)))
  return out

/-- A tool call as argv. -/
def argvOf (b : Base) (name : String) (args : Json) : Except String (List String) := do
  let getStr := fun (k : String) => match args.getObjVal? k with
    | .ok (.str s) => some s
    | .ok (.num n) => some (toString n)
    | .ok (.bool v) => some (toString v)
    | _ => none
  let need := fun (k : String) => match getStr k with
    | some v => Except.ok v
    | none => Except.error s!"missing argument {k}"
  let rowArg := fun (k : String) => match args.getObjVal? k with
    | .ok j => Except.ok j.compress
    | .error _ => Except.error s!"missing argument {k}"
  match name with
  | "schema" => return ["schema"]
  | "version" => return ["version"]
  | "log" => return ["log"] ++ (match getStr "limit" with | some n => [n] | none => [])
  | "migrate_status" => return ["migrate", "status"]
  | "seed" => return ["seed"]
  | _ =>
    if let some q := b.queries.find? (fun q => s!"query_{q.name}" == name) then
      let vals ← q.params.mapM fun (n, _) => need n
      return ["query", q.name] ++ vals
    let verbs := ["rows_", "get_", "insert_", "update_", "delete_"]
    match verbs.find? (name.startsWith ·) with
    | some v =>
        let t := (name.drop v.length).toString
        unless b.tables.any (·.name == t) do throw s!"unknown table {t}"
        match v with
        | "rows_" =>
            let eqs ← match args.getObjVal? "eq" with
              -- only the key's absence means "no filter"; anything present
              -- must be an array of strings, else the caller's filter would
              -- be silently dropped
              | .error _ => pure []
              | .ok (.arr a) =>
                  let vs ← a.mapM fun e =>
                    match e with | .str s => pure s | _ => throw "eq must be an array of strings"
                  pure (vs.toList)
              | .ok _ => throw "eq must be an array of strings"
            let limit ← match args.getObjVal? "limit" with
              | .error _ => pure []
              | .ok (.str s) => pure ["--limit", s]
              | .ok (.num n) => pure ["--limit", toString n]
              | .ok _ => throw "limit must be a string"
            return ["rows", t] ++ (eqs.flatMap fun e => ["--eq", e]) ++ limit
        | "get_" => return ["get", t, ← need "id"]
        | "insert_" => return ["insert", t, ← rowArg "row"]
        | "update_" => return ["update", t, ← need "id", ← rowArg "row"]
        | _ => return ["delete", t, ← need "id"]
    | none => throw s!"unknown tool {name}"

private def result (id : Json) (r : Json) : Json :=
  Json.mkObj [("jsonrpc", str "2.0"), ("id", id), ("result", r)]

private def rpcError (id : Json) (code : Int) (m : String) : Json :=
  Json.mkObj [("jsonrpc", str "2.0"), ("id", id),
    ("error", Json.mkObj [("code", Lean.toJson code), ("message", str m)])]

/-- A tool result: the handler's JSON as text content; `isError` mirrors `ok`. -/
private def toolResult (id : Json) (j : Json) : Json :=
  let ok := (j.getObjValAs? Bool "ok").toOption == some true
  result id <| Json.mkObj [
    ("content", Json.arr #[Json.mkObj [("type", str "text"), ("text", str j.pretty)]]),
    ("structuredContent", j),
    ("isError", Json.bool (!ok))]

/-- One message → the optional response. A JSON-RPC notification (no `id`)
    gets no reply of any kind, whatever the method — `tools/call` is never
    executed as a notification. A request whose `id` is `null` is invalid
    (-32600), not a notification. -/
def respond (b : Base) (inst : Instance) (sess : Cli.Session) (msg : Json) : IO (Option Json) := do
  let id? := (msg.getObjVal? "id").toOption
  -- no `id`: a notification, never answered, whatever the method
  if id?.isNone then
    unless msg matches .obj _ do
      -- a non-object message cannot even claim to be a notification
      return some (rpcError .null (-32600) "invalid request: not an object")
    return none
  if let some .null := id? then
    return some (rpcError .null (-32600) "invalid request: id must be a string or a number")
  let id := id?.getD Json.null
  let method := (msg.getObjValAs? String "method").toOption.getD ""
  let params := (msg.getObjVal? "params").toOption.getD (Json.mkObj [])
  match method with
  | "initialize" => pure <| some <| result id <| Json.mkObj [
      ("protocolVersion", str ((params.getObjValAs? String "protocolVersion").toOption.getD "2025-06-18")),
      ("capabilities", Json.mkObj [("tools", Json.mkObj [("listChanged", Json.bool false)])]),
      ("serverInfo", Json.mkObj [("name", str s!"leandb-{b.name}"), ("version", str "0.3.1")]),
      ("instructions", str s!"The {b.name} base: typed tables and registered queries. Every tool is one command of the base's CLI; errors carry a typed code.")]
  | "ping" => pure <| some <| result id (Json.mkObj [])
  | "tools/list" => pure <| some <| result id (Json.mkObj [("tools", Json.arr (tools b))])
  | "tools/call" =>
      let name := (params.getObjValAs? String "name").toOption.getD ""
      let args := (params.getObjVal? "arguments").toOption.getD (Json.mkObj [])
      match argvOf b name args with
      | .error m => pure <| some <| rpcError id (-32602) m
      | .ok argv => pure <| some <| toolResult id (← b.handle inst sess argv)
  | _ => pure <| some <| rpcError id (-32601) s!"method not found: {method}"

/-- Serve MCP on stdio against one session until EOF. -/
def serve (b : Base) (inst : Instance) : IO UInt32 := do
  match ← Cli.Session.open b inst with
  | .error e =>
      IO.eprintln e.toJson.compress
      return e.exitCode
  | .ok sess =>
      let stdin ← IO.getStdin
      let out ← IO.getStdout
      let reader ← Cli.LineReader.new stdin
      repeat
        match ← reader.next with
        | .eof => break
        | .tooLong =>
            out.putStrLn (rpcError Json.null (-32700) s!"request line exceeds {Cli.defaultMaxLineBytes} bytes").compress
            out.flush
        | .undecodable =>
            out.putStrLn (rpcError Json.null (-32700) "request line is not valid UTF-8").compress
            out.flush
        | .line rawLine =>
          let line := rawLine.trimAscii.toString
          if line.isEmpty then continue
          match Json.parse line with
          | .error m =>
              out.putStrLn (rpcError Json.null (-32700) s!"parse error: {m}").compress
          | .ok msg =>
              match ← respond b inst sess msg with
              | none => pure ()
              | some reply =>
                  out.putStrLn reply.compress
                  out.flush
      return 0

initialize
  Cli.mcpServer.set (some serve)

end LeanDb.Mcp
