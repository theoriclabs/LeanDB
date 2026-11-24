import Tickets
import Eats
import LeanDbHttp

/-! # dashboard — importing bases into another project

Not a base. `Tickets` and `Eats` are ordinary Lake dependencies; this
program gets their types, their `base` values and their query defs, and
uses them three ways:

- **in-process**, against each base's instance file: `Base.withInstance`
  opens the file with the base's own schema check and runs the query
  defs directly — the same `DbM` code the bases' CLIs run;
- **over the stdio wire**, against a served base: `Client.connect` spawns
  `tickets serve`, shakes hands on the fingerprint, and `client%
  slaBreached` is the query's signature with `DbM` replaced by
  `ClientM` — arguments render through `CliRender`, results decode
  through `QueryIn`, so the remote call is typed like the local one;
- **over HTTP**, against `tickets serve --http`, using the optional
  `LeanDbHttp` package and its libcurl-backed `leanhttp`
  transport. The same typed stub and result checks are unchanged.

Run from `examples/dashboard` after `lake build` here and
`lake build tickets` in `../tickets`. -/

open LeanDb

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw <| IO.userError s!"FAIL: {message}"

private def expectOk (r : Except DbError α) (what : String) : IO α := do
  match r with
  | .ok a => pure a
  | .error e => throw <| IO.userError s!"FAIL: {what}: {e}"

private def ticketsDb : System.FilePath := ".lake" / "dashboard_tickets.sqlite"
private def eatsDb : System.FilePath := ".lake" / "dashboard_eats.sqlite"
private def httpPort : UInt16 := 7435

/-- The remote stub, typed from the def's signature. -/
def slaBreachedRemote := client% Tickets.slaBreached

private def connectHttpEventually (url fingerprint : String)
    (config : LeanHttp.Session.Config) : IO (Except DbError Client) := do
  for _ in [0:40] do
    match ← HttpClient.connectUrl url fingerprint config with
    | .ok client => return .ok client
    | .error (.transport _) => IO.sleep 50
    | .error e => return .error e
  return .error (.transport s!"HTTP server at {url} did not become ready")

def main : IO UInt32 := do
  for p in [ticketsDb, eatsDb] do
    if ← p.pathExists then IO.FS.removeFile p
  -- in-process: two bases, two instances, their own seeds and queries
  let tickets := Instance.ofPath ticketsDb
  let eats := Instance.ofPath eatsDb
  discard <| expectOk (← Tickets.base.withInstance tickets Tickets.seed) "seed tickets"
  discard <| expectOk (← Eats.base.withInstance eats (do Eats.seed; Eats.seedOffers)) "seed eats"
  let open_ ← expectOk (← Tickets.base.withInstance tickets Tickets.openTickets) "openTickets"
  check (open_.size > 0) "open tickets in-process"
  let dinner ← expectOk (← Eats.base.withInstance eats
    (Eats.openFor ⟨"tiramisu"⟩ .fri (Eats.Clock.hm 21 30))) "openFor"
  check (dinner.size > 0) "tiramisu on Friday night in-process"
  let local_ ← expectOk (← Tickets.base.withInstance tickets (Tickets.slaBreached ⟨1700000000⟩)) "local slaBreached"
  -- over stdio: the same query through a served tickets
  let exe : System.FilePath := ".." / "tickets" / ".lake" / "build" / "bin" / "tickets"
  let client ← expectOk (← Client.connect exe (fingerprint Tickets.base.specs) ["--db", ticketsDb.toString]) "connect"
  let remote ← expectOk (← (slaBreachedRemote ⟨1700000000⟩).run client) "remote slaBreached"
  check (remote.size == local_.size) s!"remote and local agree: {remote.size} vs {local_.size}"
  check ((remote.map fun (t, u) => (t.id.toInt64, u.id.toInt64)) == (local_.map fun (t, u) => (t.id.toInt64, u.id.toInt64)))
    "same rows, same ids"
  -- a wrong fingerprint is refused at the handshake
  match ← Client.connect exe "not-this-schema" ["--db", ticketsDb.toString] with
  | .ok c => c.close; throw <| IO.userError "FAIL: handshake must refuse a foreign fingerprint"
  | .error (.schemaMismatch ..) => pure ()
  | .error e => throw <| IO.userError s!"FAIL: unexpected handshake error {e}"
  -- any argv works through the client too
  let rows ← expectOk (← (Client.argv ["rows", "ticket", "--limit", "2"]).run client) "rows over the wire"
  check ((rows.getObjValAs? Nat "count").toOption == some 2) "two rows over the wire"
  client.close

  -- over HTTP: the same stub and data, through the optional adapter.
  let httpChild ← IO.Process.spawn {
    cmd := exe.toString
    args := #["--db", ticketsDb.toString, "serve", "--http", toString httpPort,
      "--auth-token", "dashboard-check"]
    stdin := .null
    stdout := .null
    stderr := .inherit }
  try
    -- A trailing slash is accepted without producing `//version`.
    let url := s!"http://127.0.0.1:{httpPort}/"
    let config : LeanHttp.Session.Config := {
      headers := Std.Http.Headers.empty.insert! "Authorization" "Bearer dashboard-check" }
    let httpClient ← expectOk
      (← connectHttpEventually url (fingerprint Tickets.base.specs) config) "connect over HTTP"
    let httpRemote ← expectOk
      (← (slaBreachedRemote ⟨1700000000⟩).run httpClient) "HTTP slaBreached"
    check ((httpRemote.map fun (t, u) => (t.id.toInt64, u.id.toInt64)) ==
      (local_.map fun (t, u) => (t.id.toInt64, u.id.toInt64)))
      "HTTP and local return the same rows and ids"
    match ← HttpClient.connectUrl url "not-this-schema" config with
    | .ok c => c.close; throw <| IO.userError "FAIL: HTTP handshake must refuse a foreign fingerprint"
    | .error (.schemaMismatch ..) => pure ()
    | .error e => throw <| IO.userError s!"FAIL: unexpected HTTP handshake error {e}"
    httpClient.close
  finally
    try httpChild.kill catch _ => pure ()
    try discard <| httpChild.wait catch _ => pure ()
  IO.println "dashboard: all checks passed"
  return 0
