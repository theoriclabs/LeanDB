import LeanDb.Http
import LeanDb.Client

namespace LeanDb.Host

/-! # `leandb host`: many bases, one port

Each base is its own binary (its types are compiled in), so hosting many
means supervising many: `leandb host --port P <name>=<exe>[,--db path]…`
(a literal comma in the exe path or an argument is escaped `\,`),
spawns every base in `serve` mode (JSON lines over stdio), keeps one
connection each, and serves `/bases/<name>/…` with the same routes a
base serves alone — the argv is the wire between the two processes.
`GET /bases` lists them with their fingerprints. -/

open Lean (Json)

structure Child where
  name : String
  client : Client
  /-- The pipe carries one request at a time: the same dispatch gate as
      `serve --http` (#79), so waiting on a child's `backup` does not pin
      a host worker thread. -/
  gate : Http.Gate
  fingerprint : String

/-- Split on raw commas; `\,` is a literal comma and the backslash is
    consumed (issue #62: an exe path like `/opt/my,tools/leandb` was
    inexpressible — a raw comma always split the launch line). -/
def splitCommas (s : String) : List String :=
  let rec go : List Char → String → List String → List String
    | [], acc, segs => (acc :: segs).reverse
    | ',' :: rest, acc, segs => go rest "" (acc :: segs)
    | '\\' :: ',' :: rest, acc, segs => go rest (acc.push ',') segs
    | c :: rest, acc, segs => go rest (acc.push c) segs
  go s.toList "" []

/-- The `(name, exe, args)` of one host spec `name=exe[,arg,…]`: the
    first `=` separates name from launch line, raw commas split it, and
    `\,` is a literal comma (issue #62). -/
def parseSpec (spec : String) : Except String (String × String × List String) :=
  match spec.splitOn "=" with
  | name :: rest =>
      match splitCommas (String.intercalate "=" rest) with
      | exe :: args =>
          let name := String.intercalate "," (splitCommas name)
          if name.isEmpty || exe.isEmpty then
            .error s!"expected name=exe[,args], got {spec}"
          else .ok (name, exe, args)
      | [] => .error s!"expected name=exe[,args], got {spec}"
  | [] => .error s!"expected name=exe[,args], got {spec}"

/-- `name=path/to/exe[,arg,…]` → spawn and handshake-free connect (the
    host trusts what the base reports). No handshake deadline yet (issue
    #62, facet 2, open): the `version` read below blocks until the child
    writes or closes, so a base that spawns silent wedges the host
    pre-bind. -/
def spawn (spec : String) : IO (Except String Child) := do
  match parseSpec spec with
  | .error m => return .error m
  | .ok (name, exe, args) =>
      let cfg : IO.Process.SpawnArgs := {
        cmd := exe
        args := (args ++ ["serve"]).toArray
        stdin := .piped
        stdout := .piped
        stderr := .inherit }
      try
        let child ← IO.Process.spawn cfg
        let client := Client.ofProcess child
        match ← client.rpc ["version"] with
        | .error e => client.close; return .error s!"{name}: could not query {exe}: {e}"
        | .ok v =>
            let fp := (v.getObjValAs? String "code_fingerprint").toOption.getD ""
            return .ok { name, client := { client with fingerprint := fp }, gate := ← Http.Gate.new, fingerprint := fp }
      catch e =>
        return .error s!"{name}: could not start {exe}: {e}"

def Child.call (c : Child) : List String → Std.Async.ContextAsync Json :=
  c.gate.dispatch fun argv => do
    match ← c.client.rpc argv with
    | .ok json => return json
    | .error e => return e.toJson

/-- The host's argv: the `--port` string survives verbatim and resolves
    through `Cli.portOf` at `run` (issue #56: an in-parser `Nat.toUInt16`
    bound port mod 2^16 while the banner echoed the raw number). -/
def parseArgs : List String →
    Except String (Option String × String × Option String × List String)
  | [] => .ok (none, "127.0.0.1", none, [])
  | "--port" :: p :: rest => do let (_, h, t, specs) ← parseArgs rest; return (some p, h, t, specs)
  | "--bind" :: h :: rest => do let (p, _, t, specs) ← parseArgs rest; return (p, h, t, specs)
  | "--auth-token" :: t :: rest => do let (p, h, _, specs) ← parseArgs rest; return (p, h, some t, specs)
  | spec :: rest => do let (p, h, t, specs) ← parseArgs rest; return (p, h, t, spec :: specs)

/-- `leandb host --port P [--bind H] [--auth-token <t>] name=exe[,args]…
    (a literal comma in exe or an arg is escaped `\,`) -/
def run (args : List String) : IO UInt32 := do
  let usage := "host --port <port> [--bind <host>] [--auth-token <t>] <name>=<exe>[,<arg>,…]…  (a literal comma in exe or an arg is escaped \\,)"
  match parseArgs args with
  | .error m =>
      IO.eprintln (Json.mkObj [("ok", Json.bool false), ("code", Json.str "usage"), ("message", Json.str s!"{m}; {usage}")]).compress
      return 3
  | .ok (portStr?, host, token?, specs) =>
      let some portStr := portStr? | do
        IO.eprintln (Json.mkObj [("ok", Json.bool false), ("code", Json.str "usage"), ("message", Json.str usage)]).compress
        return 3
      let port ← match Cli.portOf portStr with
        | .ok p => pure p
        | .error m =>
            IO.eprintln (Json.mkObj [("ok", Json.bool false), ("code", Json.str "usage"), ("message", Json.str s!"{m}; {usage}")]).compress
            return 3
      if specs.isEmpty then
        IO.eprintln (Json.mkObj [("ok", Json.bool false), ("code", Json.str "usage"), ("message", Json.str s!"no bases given; {usage}")]).compress
        return 3
      let mut children : Array Child := #[]
      let mut spawnErr : Option String := none
      for spec in specs do
        match ← spawn spec with
        | .ok c => children := children.push c
        | .error m =>
            spawnErr := some m
            break
      if let some m := spawnErr then
        -- a later spec failing must not leave earlier children running
        -- detached, holding their SQLite files (issue #62)
        IO.eprintln (Json.mkObj [("ok", Json.bool false), ("code", Json.str "usage"), ("message", Json.str m)]).compress
        children.forM fun c => c.client.close
        return 3
      let list := Json.mkObj [("ok", Json.bool true), ("bases", Json.arr (children.map fun c =>
        Json.mkObj [("name", Json.str c.name), ("fingerprint", Json.str c.fingerprint)]))]
      let bases := fun (name : String) =>
        (children.find? (·.name == name)).map fun c => (c.fingerprint, c.call)
      try
        let code ← Http.serveHosted host port (← Http.Auth.resolve token?) list bases <|
          Json.mkObj [("ok", Json.bool true),
            ("serving", Json.str s!"http://{host}:{port}"),
            ("bases", Json.arr (children.map fun c => Json.str c.name))]
        children.forM fun c => c.client.close
        return code
      catch e =>
        -- bind failure or any throw from the serve loop closes the
        -- children the host would otherwise orphan (issue #62)
        children.forM fun c => c.client.close
        IO.eprintln (Json.mkObj [("ok", Json.bool false), ("code", Json.str "usage"), ("message", Json.str (toString e))]).compress
        return 3

end LeanDb.Host
