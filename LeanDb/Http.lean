import Std.Http
import Std.Async.Timer
import LeanDb.Cli

namespace LeanDb.Http

/-! # HTTP over the handler

`<base> serve --http <port>` puts `Base.handle` behind HTTP/1.1 using the
toolchain's `Std.Http.Server`. Every route is sugar over one argv: the
typed routes below and `POST /rpc` (a JSON array of argv strings) reach
the same function, so the surface is exactly the CLI's. Responses are
the handler's JSON; the status code derives from the response `code`.
The connection is one SQLite handle, so requests run one at a time,
in arrival order, through a dispatch gate (`Gate`) that waits without
pinning a worker thread on a native lock. The long file-level verbs —
`backup`, `restore`, and the destructive `migrate apply` / `migrate
rollback` — hold it for their whole run; any other verb that has waited
a bounded time behind them answers `503` with `Retry-After` instead.
Behind an ordinary verb, however slow, requests queue as they always
did. `/healthz` never touches the gate. A client that sends
`X-LeanDb-Fingerprint` is refused
with `schema_mismatch` (409) when it was compiled against another
schema. -/

open Std Std.Http Std.Async
open Lean (Json)

/-- HTTP status for a handler response. -/
def statusOf (j : Json) : Status :=
  if (j.getObjValAs? Bool "ok").toOption == some true then .ok
  else match (j.getObjValAs? String "code").toOption with
    | some "usage" | some "decode" => .badRequest
    | some "unauthorized" => .unauthorized
    | some "not_found" => .notFound
    | some "stale" | some "restricted" | some "duplicate" | some "missing_ref"
    | some "schema_mismatch" | some "unknown_lineage" | some "migrate" => .conflict
    | some "read_only" => .forbidden
    | some "busy" => .serviceUnavailable
    | some "poisoned" => .internalServerError
    | _ => .internalServerError

private def usage (m : String) : Nat × String := (400, m)


/-- Resolve a request to argv. `segs` are the decoded path segments,
    `query` the decoded query pairs, `body` the request body if any. -/
def route (method : String) (segs : List String) (query : List (String × String))
    (body : Option String) : Except (Nat × String) (List String) := do
  let eqs := query.filter (·.1 == "eq") |>.flatMap fun (_, v) => ["--eq", v]
  let limit := match query.lookup "limit" with | some n => ["--limit", n] | none => []
  let bodyStr ← match body with
    | some s => pure s
    | none => pure ""
  let needBody := fun (what : String) => do
    if bodyStr.trimAscii.isEmpty then throw (usage s!"{what} needs a JSON body") else pure bodyStr
  match method, segs with
  | "GET", ["schema"] => return ["schema"]
  | "GET", ["version"] => return ["version"]
  | "GET", ["help"] | "GET", [] => return ["help"]
  | "GET", ["log"] => return ["log"] ++ (match query.lookup "limit" with | some n => [n] | none => [])
  | "GET", ["tables", t] => return ["rows", t] ++ eqs ++ limit
  | "GET", ["tables", t, id] => return ["get", t, id]
  | "POST", ["tables", t] => return ["insert", t, ← needBody "insert"]
  | "PATCH", ["tables", t, id] | "PUT", ["tables", t, id] => return ["update", t, id, ← needBody "update"]
  | "DELETE", ["tables", t, id] => return ["delete", t, id]
  | "GET", "query" :: q :: args => return ["query", q] ++ args
  | "POST", ["query", q] =>
      -- {"args":["…", …]}: strings, parsed by the query's own CliArg instances
      let args ← if bodyStr.trimAscii.isEmpty then pure [] else
        match Json.parse bodyStr >>= (·.getObjValAs? (Array Json) "args") with
        | .ok arr => arr.toList.mapM fun a => match a with
            | .str s => pure s
            | .num n => pure (toString n)
            | .bool b => pure (toString b)
            | other => throw (usage s!"query argument must be a string, got {other.compress}")
        | .error m => throw (usage s!"expected \{\"args\":[…]}: {m}")
      return ["query", q] ++ args
  | "POST", ["seed"] => return ["seed"]
  | "GET", ["migrate"] | "GET", ["migrate", "status"] => return ["migrate", "status"]
  | "POST", ["migrate", "apply"] =>
      let flags := (if query.lookup "allow_destructive" == some "1" then ["--allow-destructive"] else []) ++
        (if query.lookup "backup" == some "0" then ["--no-backup"] else [])
      return ["migrate", "apply"] ++ flags
  | "POST", ["migrate", "rollback"] => return ["migrate", "rollback"]
  | "GET", ["migrate", "history"] => return ["migrate", "history"] ++ (match query.lookup "limit" with | some n => [n] | none => [])
  | "POST", ["backup"] => return ["backup"]
  | "POST", ["restore"] =>
      match Json.parse (← needBody "restore") >>= (·.getObjValAs? String "file") with
      | .ok f => return ["restore", f]
      | .error m => throw (usage s!"expected \{\"file\":\"…\"}: {m}")
  | "POST", ["rpc"] =>
      match Json.parse (← needBody "rpc") >>= fun j => j.getArr? >>= (·.toList.mapM (·.getStr?)) with
      | .ok argv => return argv
      | .error m => throw (usage s!"expected a JSON array of argv strings: {m}")
  | m, path => throw (404, s!"no route {m} /{String.intercalate "/" path}")

private def errJson (code : String) (m : String) : Json :=
  Json.mkObj [("ok", Json.bool false), ("code", Json.str code), ("message", Json.str m)]

private def respond (status : Status) (j : Json) : ContextAsync (Response Body.Any) := do
  let r ← (Response.withStatus status).json j.compress
  return { line := r.line, body := Body.Any.ofBody r.body, extensions := r.extensions }

/-- Where a request goes: the segments to route, the fingerprint of the
    schema behind them, and the argv dispatcher. A single served base
    resolves everything to itself; a host resolves `/bases/<name>/…`. -/
abbrev Resolver := List String → IO (Except (Nat × String)
  (List String × String × (List String → ContextAsync Json)))

/-- Access policy for a served base: open, or a bearer token every
    request must carry (`Authorization: Bearer <token>`). `/healthz` is
    always open, so an orchestrator can probe without the secret. -/
inductive Auth where
  | open
  | bearer (token : String)

/-- `--auth-token <t>` beats `$LEANDB_TOKEN`; neither means open. -/
def Auth.resolve (flag : Option String) : IO Auth := do
  match flag with
  | some t => return .bearer t
  | none =>
      match ← IO.getEnv "LEANDB_TOKEN" with
      | some t => if t.isEmpty then return .open else return .bearer t
      | none => return .open

private def authorized (auth : Auth) (req : Request Body.Stream) : Bool :=
  match auth with
  | .open => true
  | .bearer token =>
      match req.line.headers.get? (Header.Name.ofString! "authorization") with
      | some v => toString v == s!"Bearer {token}"
      | none => false

/-- Loopback bind or Host/Origin name: tokenless CSRF and DNS-rebinding
    only make sense to pin against these. -/
def isLoopbackHost (host : String) : Bool :=
  let h := host.trimAscii.toString.toLower
  h == "localhost" || h == "127.0.0.1" || h.startsWith "127."

/-- Strip an optional `:port` from a Host header. -/
def hostName (header : String) : String :=
  let s := header.trimAscii.toString
  match s.splitOn ":" with
  | h :: _ => h
  | [] => s

/-- `application/json` or `application/json; charset=…`. -/
def isJsonContentType (header : String) : Bool :=
  let s := header.trimAscii.toString.toLower
  s == "application/json" || s.startsWith "application/json;"

/-- Routes whose body is parsed as JSON. -/
def jsonBodyRoute (method : String) (segs : List String) : Bool :=
  match method, segs with
  | "POST", ["tables", _] => true
  | "PATCH", ["tables", _, _] | "PUT", ["tables", _, _] => true
  | "POST", ["query", _] => true
  | "POST", ["restore"] => true
  | "POST", ["rpc"] => true
  | _, _ => false

/-- Host header is required; when the server is bound to loopback the
    name must also be loopback (`localhost` / `127.0.0.1`), so a
    DNS-rebound page cannot become same-origin with the server. -/
def hostAllowed (boundHost header : String) : Bool :=
  let name := hostName header
  if isLoopbackHost boundHost then isLoopbackHost name else !name.isEmpty

/-- An `Origin` header, when present, must agree with a loopback bind.
    Absent Origin (curl, agent harnesses) is allowed. -/
def originAllowed (boundHost : String) : Option String → Bool
  | none => true
  | some origin =>
      if !isLoopbackHost boundHost then true
      else
        let o := origin.trimAscii.toString.toLower
        o.startsWith "http://127.0.0.1" || o.startsWith "https://127.0.0.1" ||
          o.startsWith "http://localhost" || o.startsWith "https://localhost"

/-- Default request-body budget for both standalone and hosted bases: 2 MiB. -/
def defaultMaxBodyBytes : Nat := 2 * 1024 * 1024

/-- Parse the startup setting; an invalid value must not silently disable the limit. -/
def bodyLimitOf (value : Option String) : Except String Nat := do
  match value with
  | none => return defaultMaxBodyBytes
  | some s =>
      let some n := s.toNat? | throw "LEANDB_HTTP_MAX_BODY_BYTES must be a positive integer"
      if n == 0 then throw "LEANDB_HTTP_MAX_BODY_BYTES must be a positive integer"
      return n

/-- Keep the framing parser's chunk budget. Leave room for the handler to
    observe the first chunk over its payload budget: Std closes the body
    stream on a framing error without distinguishing that from normal EOF. -/
def serverConfig (maxBodyBytes : Nat) : Std.Http.Config :=
  let defaults : Std.Http.Config := {}
  { generateDate := false,
    maxBodySize := max defaults.maxBodySize (maxBodyBytes + defaults.maxChunkSize) }

/-- Stop before appending a chunk that would exceed the budget. This also
    protects callers that use the handler with their own HTTP configuration. -/
private partial def readBody (stream : Body.Stream) (limit : Nat) :
    ContextAsync (Option ByteArray) := do
  if let some (.fixed n) ← stream.getKnownSize then
    if n > limit then return none
  let rec loop (bytes : ByteArray) : ContextAsync (Option ByteArray) := do
    match ← Body.Stream.NextChunk.nextChunk stream with
    | none => return some bytes
    | some chunk =>
        if bytes.size + chunk.data.size > limit then return none
        loop (bytes ++ chunk.data)
  loop ByteArray.empty

/-- One request through the resolver. `boundHost` is the bind address
    (`127.0.0.1` by default): Host/Origin are pinned to loopback when
    that is where the server listens. `/healthz` stays open. -/
def handleRequestWithLimit (maxBodyBytes : Nat) (auth : Auth) (resolve : Resolver)
    (req : Request Body.Stream) (boundHost : String := "127.0.0.1") :
    ContextAsync (Response Body.Any) := do
  let method := (toString req.line.method).toUpper
  let segs := (req.line.uri.path.toDecodedSegments.toList).filter (!·.isEmpty)
  -- liveness, before the secret: nothing about the base is revealed
  if segs == ["healthz"] then
    return ← respond .ok (Json.mkObj [("ok", Json.bool true)])
  -- Host / Origin: pin a loopback server so a rebound page cannot
  -- become same-origin with it. Tokenless CSRF is further blocked by
  -- requiring `Content-Type: application/json` on JSON-body routes
  -- (that is not a "simple" type, so browsers preflight).
  match req.line.headers.get? (Header.Name.ofString! "host") with
  | none =>
      return ← respond .badRequest (errJson "usage" "Host header required")
  | some host =>
      unless hostAllowed boundHost (toString host) do
        return ← respond .forbidden (errJson "usage" s!"Host {String.quote (toString host)} is not this server")
  if let some origin := req.line.headers.get? (Header.Name.ofString! "origin") then
    unless originAllowed boundHost (some (toString origin)) do
      return ← respond .forbidden (errJson "usage" s!"Origin {String.quote (toString origin)} is not this server")
  unless authorized auth req do
    let r ← respond .unauthorized (errJson "unauthorized" "bearer token required (Authorization: Bearer <token>)")
    return { r with line := { r.line with headers := r.line.headers.insert (Header.Name.ofString! "www-authenticate") (Header.Value.ofString! "Bearer") } }
  let query := req.line.uri.query.toList.filterMap fun (k, v) => do
    let k ← k.decode
    some (k, (v.bind (·.decode)).getD "")
  let some bytes ← readBody req.body maxBodyBytes |
    return ← respond .payloadTooLarge (errJson "usage" "request body too large")
  let body := if bytes.isEmpty then none else String.fromUTF8? bytes
  if jsonBodyRoute method segs && body.isSome then
    match req.line.headers.get? (Header.Name.ofString! "content-type") with
    | some ct =>
        unless isJsonContentType (toString ct) do
          return ← respond .unsupportedMediaType
            (errJson "usage" "Content-Type must be application/json")
    | none =>
        return ← respond .unsupportedMediaType
          (errJson "usage" "Content-Type must be application/json")
  match ← resolve segs with
  | .error (404, m) => respond .notFound (errJson "usage" m)
  | .error (_, m) => respond .badRequest (errJson "usage" m)
  | .ok (segs, fingerprint, dispatch) =>
      -- the handshake: a client compiled against another schema is told so
      if let some claimed := req.line.headers.get? (Header.Name.ofString! "x-leandb-fingerprint") then
        unless toString claimed == fingerprint do
          return ← respond .conflict (DbError.schemaMismatch (toString claimed) fingerprint).toJson
      match route method segs query body with
      | .error (404, m) => respond .notFound (errJson "usage" m)
      | .error (_, m) => respond .badRequest (errJson "usage" m)
      | .ok argv =>
          let j ← dispatch argv
          let status := statusOf j
          let r ← respond status j
          -- `busy`: the gate timed a fast verb out behind a long one, or a
          -- restore/rollback found another writer on the file (#76). Both
          -- clear up on their own, so tell the client to retry
          if status == .serviceUnavailable then
            let headers :=
              r.line.headers.insert (Header.Name.ofString! "retry-after")
                (Header.Value.ofString! "1")
            return { r with line := { r.line with headers } }
          return r

/-- One request with the default body budget, for direct handler callers. -/
def handleRequest (auth : Auth) (resolve : Resolver) (req : Request Body.Stream) :
    ContextAsync (Response Body.Any) :=
  handleRequestWithLimit defaultMaxBodyBytes auth resolve req


/-- The verbs that hold the engine for their whole run (#79): `backup`
    vacuums the whole instance into a copy, `restore` swaps the instance
    file and reopens, and the destructive migration steps rewrite it.
    Nothing else may observe the instance mid-flight, so these cannot
    yield; `POST /rpc` argv is classified by the same rule. -/
def longVerb (argv : List String) : Bool :=
  match argv with
  | "backup" :: _ | "restore" :: _
  | "migrate" :: "apply" :: _ | "migrate" :: "rollback" :: _ => true
  | _ => false

/-- How a long verb is named in the `busy` message. -/
private def longVerbName : List String → String
  | "migrate" :: step :: _ => s!"migrate {step}"
  | verb :: _ => verb
  | [] => ""

/-- Who holds the engine: nobody, an ordinary verb, or a long verb
    (named, so a request that gives up can say what it waited for). -/
inductive Gate.Holder where
  | free
  | fast
  | long (verb : String)

/-- The whole gate, swapped atomically through one `IO.Ref`. -/
structure Gate.State where
  holder : Gate.Holder := .free
  /-- Tickets of the waiting requests, oldest first. -/
  line : Array Nat := #[]
  /-- The next ticket to hand out. -/
  next : Nat := 0

/-- The dispatch gate (#79): one holder at a time == the engine. `serve`
    used to hold a native `Std.Mutex` across the whole handler, so a
    multi-second `backup` pinned every queued request's worker thread and
    starved `/healthz`. Now a request takes a ticket and polls for its
    turn, sleeping between attempts with `Std.Async.sleep`, which yields
    the worker instead of blocking it. The engine goes to the oldest
    ticket, so a stream of newcomers cannot starve a waiter. Long verbs
    hold the gate for their whole handler — the instance must not be
    observed mid-copy or mid-swap — and wait as long as it takes. Any
    other verb also waits as long as the holder is an ordinary verb (a
    slow query, `seed`, `migrate status` queue as they did behind the
    mutex), but once it has spent `fastTimeoutMs` behind long verbs it
    leaves the line and answers `busy` (mapped to `503` + `Retry-After`).
    The engine is always released in a `finally`, so even a throwing
    handler cannot take the gate down. -/
structure Gate where
  /-- Who holds the engine, and the line waiting for it. -/
  state : IO.Ref Gate.State
  /-- How long a fast verb waits behind long verbs before answering 503. -/
  fastTimeoutMs : Nat := 5000
  /-- Sleep between acquisition attempts. -/
  pollMs : Nat := 5

def Gate.new (fastTimeoutMs : Nat := 5000) : BaseIO Gate :=
  return { state := ← IO.mkRef {}, fastTimeoutMs }

/-- How many requests are waiting for the engine. -/
def Gate.waiting (g : Gate) : BaseIO Nat :=
  return (← g.state.get).line.size

/-- Join the back of the line; the ticket is the caller's place in it. -/
private def Gate.join (g : Gate) : BaseIO Nat :=
  g.state.modifyGet fun st =>
    (st.next, { st with line := st.line.push st.next, next := st.next + 1 })

/-- Leave the line. A no-op once the ticket has taken the engine. -/
private def Gate.leave (g : Gate) (ticket : Nat) : BaseIO Unit :=
  g.state.modify fun st => { st with line := st.line.erase ticket }

/-- Take the engine as `as` if it is free and `ticket` is first in line:
    `none` once the caller holds it, otherwise whoever holds it now. -/
private def Gate.tryTake (g : Gate) (ticket : Nat) (as : Gate.Holder) :
    BaseIO (Option Gate.Holder) :=
  g.state.modifyGet fun st =>
    if st.holder matches .free && st.line[0]? == some ticket then
      (none, { st with holder := as, line := st.line.erase ticket })
    else (some st.holder, st)

/-- Hand the engine back; the oldest waiter takes it on its next attempt. -/
private def Gate.release (g : Gate) : BaseIO Unit :=
  g.state.modify fun st => { st with holder := .free }

/-- Wait in line until `ticket` takes the engine as `as`. `waited` is the
    time spent so far behind long verbs, `since` the last attempt: a fast
    verb gives up once `waited` reaches `fastTimeoutMs`, and returns the
    long verb holding the engine at that point. -/
private partial def Gate.wait (g : Gate) (ticket : Nat) (as : Gate.Holder)
    (waited since : Nat) : ContextAsync (Option String) := do
  let some holder ← g.tryTake ticket as | return none
  let now ← IO.monoMsNow
  -- only time behind a long verb counts against a fast verb
  let behindLong := match as, holder with
    | .fast, .long verb => some verb
    | _, _ => none
  let waited := if behindLong.isSome then waited + (now - since) else waited
  if let some verb := behindLong then
    if waited ≥ g.fastTimeoutMs then return some verb
  Std.Async.sleep (Std.Time.Millisecond.Offset.ofNat g.pollMs)
  g.wait ticket as waited now

/-- Run one argv behind the gate. Long verbs wait without a deadline;
    fast verbs wait without one too, except that `fastTimeoutMs` spent
    behind long verbs gets them `busy`. The ticket leaves the line and
    the engine is released in a `finally` on every path. -/
def Gate.dispatch (g : Gate) (h : List String → ContextAsync Json) :
    List String → ContextAsync Json := fun argv => do
  let as : Gate.Holder := if longVerb argv then .long (longVerbName argv) else .fast
  let ticket ← g.join
  let gaveUp ← try g.wait ticket as 0 (← IO.monoMsNow) finally g.leave ticket
  if let some verb := gaveUp then
    return (DbError.busy s!"the engine is busy with a long operation ({verb}); \
gave up after {g.fastTimeoutMs} ms, retry shortly").toJson
  try
    h argv
  finally
    g.release

private def parseHost (host : String) : Except String Net.IPv4Addr :=
  match host.splitOn "." |>.map (·.toNat?) with
  | [some a, some b, some c, some d] =>
      if a < 256 && b < 256 && c < 256 && d < 256 then
        .ok (Net.IPv4Addr.ofParts a.toUInt8 b.toUInt8 c.toUInt8 d.toUInt8)
      else .error s!"bad IPv4 address {host}"
  | _ => .error s!"expected a dotted IPv4 address, got {host}"

/-- Serve a resolver on `host:port` until shutdown. -/
def serveResolver (host : String) (port : UInt16) (auth : Auth) (resolve : Resolver) (banner : Json) : IO UInt32 := do
  -- tokenless mode is loopback-dev-only: a non-loopback bind with no
  -- token is the CSRF/DNS-rebinding surface (#40)
  match auth with
  | .open =>
      unless isLoopbackHost host do
        IO.eprintln (errJson "usage"
          "tokenless HTTP is loopback-only; pass --auth-token / $LEANDB_TOKEN, or --bind 127.0.0.1").compress
        return 3
  | .bearer _ => pure ()
  let maxBodyBytes ← match bodyLimitOf (← IO.getEnv "LEANDB_HTTP_MAX_BODY_BYTES") with
    | .ok n => pure n
    | .error m =>
        IO.eprintln (errJson "usage" m).compress
        return 3
  let ip ← match parseHost host with
    | .ok ip => pure ip
    | .error m =>
        IO.eprintln (errJson "usage" m).compress
        return 3
  let addr : Net.SocketAddress := .v4 { addr := ip, port }
  let handler := Std.Http.Server.Handler.ofFn (fun req =>
    handleRequestWithLimit maxBodyBytes auth resolve req host)
  let banner := banner.mergeObj (Json.mkObj [("max_body_bytes", Lean.toJson maxBodyBytes)])
  let banner := match auth with
    | .open => banner.mergeObj (Json.mkObj [("auth", Json.str "open")])
    | .bearer _ => banner.mergeObj (Json.mkObj [("auth", Json.str "bearer")])
  IO.eprintln banner.compress
  -- No `Date` header: the server would compute it through `Std.Time`,
  -- which needs zoneinfo, and a minimal container has none — every
  -- response then dies before its first byte. An API needs no Date.
  let config := serverConfig maxBodyBytes
  Async.block do
    let server ← Std.Http.Server.serve addr handler config
    server.waitShutdown
  return 0

/-- Serve one dispatcher (a single base). -/
def serveWith (host : String) (port : UInt16) (auth : Auth) (fingerprint : String)
    (dispatch : List String → ContextAsync Json) (banner : Json) : IO UInt32 :=
  serveResolver host port auth (fun segs => return .ok (segs, fingerprint, dispatch)) banner

/-- Serve many bases under `/bases/<name>/…`; `GET /bases` lists them.
    `bases name` gives a base's fingerprint and dispatcher. -/
def serveHosted (host : String) (port : UInt16) (auth : Auth) (list : Json)
    (bases : String → Option (String × (List String → ContextAsync Json))) (banner : Json) : IO UInt32 :=
  serveResolver host port auth (fun segs => do
    match segs with
    | [] | ["bases"] => return .ok ([], "", fun _ => pure list)
    | "bases" :: name :: rest =>
        match bases name with
        | some (fp, dispatch) => return .ok (rest, fp, dispatch)
        | none => return .error (404, s!"no base {name}")
    | _ => return .error (404, "routes live under /bases/<name>/…")) banner

/-- `<base> serve --http <port> [--bind <host>] [--auth-token <t>]`. -/
def serve (b : Base) (inst : Instance) (host : String) (port : UInt16) (auth : Auth) : IO UInt32 := do
  match ← Cli.Session.open b inst with
  | .error e =>
      IO.eprintln e.toJson.compress
      return e.exitCode
  | .ok sess =>
      -- #79: the session value is immutable (the connection and the
      -- drift gate live in IO.Refs inside it), so the gate is the only
      -- thing that must serialize dispatch.
      let gate ← Gate.new
      let fp := fingerprint b.specs
      let dispatch := gate.dispatch fun argv =>
        (b.handle inst sess argv : ContextAsync Json)
      serveWith host port auth fp dispatch <| Json.mkObj [("ok", Json.bool true),
        ("serving", Json.str s!"http://{host}:{port}"), ("base", Json.str b.name),
        ("instance", Json.str inst.path.toString), ("fingerprint", Json.str fp)]

initialize
  Cli.httpServer.set (some fun b inst host port token? => do
    serve b inst host port (← Auth.resolve token?))

end LeanDb.Http
