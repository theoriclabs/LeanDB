# LeanDB HTTP client

`LeanDbHttp` provides an optional libcurl-backed HTTP transport for
`LeanDb.Client`. It ships under the same Git tag as LeanDB. Adding this
package also brings in the matching LeanDB engine.

Add the following requirement to your `lakefile.toml`. If your project also
declares a direct LeanDB requirement, pin it to the same release.

```toml
[[require]]
name = "leandb_http"
git = { url = "https://github.com/theoriclabs/LeanDB", subDir = "packages/leandb-http" }
rev = "v0.8.0"
```

Run `lake update`, then import `LeanDbHttp`. The HTTP package uses the
[LeanHttp build and runtime requirements](https://github.com/theoriclabs/leanhttp/tree/v0.8.0#readme).
The following example imports the bundled [Tickets base](../../examples/tickets).

```lean
import LeanDbHttp
import Tickets

open LeanDb

def slaBreachedRemote := client% Tickets.slaBreached

def example : IO (Except DbError (Array (Stored Tickets.Ticket × Stored Tickets.User))) := do
  let client ← HttpClient.connectUrl "https://db.example.com/bases/tickets"
    (fingerprint Tickets.base.specs)
  match client with
  | .error e => return .error e
  | .ok client =>
      let result ← (slaBreachedRemote ⟨1700000000⟩).run client
      client.close
      return result
```

The adapter calls `GET <base>/version` for the fingerprint handshake and
`POST <base>/rpc` thereafter. Every RPC carries `X-LeanDb-Fingerprint`.
