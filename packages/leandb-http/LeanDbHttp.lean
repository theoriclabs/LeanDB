import LeanDb.Client
import LeanHttp
import Std.Sync.Mutex

namespace LeanDb.HttpClient

open Lean (Json)
open Std.Http

private def endpoint (base : URI) (name : String) : URI :=
  let path := { base.path with absolute := true }
  let path := if path.segments.back?.any (toString · == "") then
    { path with segments := path.segments.pop }
  else path
  { base with
    path := path.append name
    query := none
    fragment := none }

private def transportError (e : LeanHttp.Error) : DbError :=
  .transport s!"HTTP transport {repr e.kind}: {e}"

private def responseJson (response : LeanHttp.Response) : Except DbError Json := do
  let some text := String.fromUTF8? response.body
    | throw (.transport s!"HTTP {response.statusCode} response is not UTF-8")
  match Json.parse text with
  | .ok json => return json
  | .error e => throw (.transport s!"HTTP {response.statusCode} response is not JSON: {e}")

private def send (session : LeanHttp.Session) (request : LeanHttp.Request) :
    IO (Except DbError Json) := do
  match ← session.request request with
  | .error e => return .error (transportError e)
  | .ok response => return responseJson response

/-- Connect a LeanDB `Client` to a base served over HTTP. `base` may be a
    standalone server root or `/bases/<name>` under `leandb host`.

    Authentication and TLS defaults belong in `config`; for bearer auth, add
    an `Authorization` header to `config.headers`. -/
def connect (base : URI) (fingerprint : String) (config : LeanHttp.Session.Config := {}) :
    IO (Except DbError Client) := do
  match ← LeanHttp.Session.new config with
  | .error e => return .error (transportError e)
  | .ok session =>
      let lock ← Std.Mutex.new ()
      let version ← lock.atomically fun _ =>
        send session { uri := endpoint base "version" }
      match version with
      | .error e => session.close; return .error e
      | .ok json =>
          match (json.getObjValAs? String "code_fingerprint").toOption with
          | none =>
              session.close
              return .error (.transport s!"HTTP base did not answer version: {json.compress}")
          | some actual =>
              if actual != fingerprint then
                session.close
                return .error (.schemaMismatch fingerprint actual)
              let fingerprintHeader := Header.Name.ofString! "X-LeanDb-Fingerprint"
              let rpc := fun (argv : List String) => lock.atomically fun _ => do
                let headers := Headers.empty.insert fingerprintHeader (Header.Value.ofString! fingerprint)
                send session {
                  method := .post
                  uri := endpoint base "rpc"
                  headers
                  body := .json (Json.arr (argv.map Json.str).toArray) }
              return .ok { rpc, fingerprint, close := session.close }

def connectUrl (base : String) (fingerprint : String)
    (config : LeanHttp.Session.Config := {}) : IO (Except DbError Client) := do
  let some uri := URI.parse? base
    | return .error (.transport s!"malformed HTTP base URI: {base}")
  connect uri fingerprint config

end LeanDb.HttpClient
