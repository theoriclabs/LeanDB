# LeanDB Cloudflare experiment gateway

Implements [protocol v1](../PROTOCOL.md). The TypeScript Worker routes to exactly
two SQLite-backed `LeanDbHost` Durable Objects, named `cf-v1:durable` and
`cf-v1:ephemeral`. Each uses the raw `ctx.container` API and owns one disposable
container. There is no `@cloudflare/containers` dependency.

`wrangler.jsonc` configures Worker/bucket `leandb-cf-exp-20261009`, account
`4203b607d58d4f83d5476e330f17a851`, `HOSTS`, `ARTIFACTS`, SQLite migration `v1`,
and the supplied digest-pinned Wybe image. The container limit is **two
standard-1 instances total**, shared by runtime and build work. Build endpoints
use the durable container; they do not allocate another builder.

## Local validation

Use the already available dependencies; do not install packages:

```sh
# Only if this link is absent:
ln -s /Users/harshwork/code/wybe/runtime/node_modules node_modules
npm run typecheck
npm test
WRANGLER_LOG_PATH=.wrangler/logs npm run dry-run
```

The tests run the real gateway code with real local SQLite and simulated native,
container, and R2 services. They cover write-ahead ordering, both injected crash
windows, DO eviction, container destruction, exact envelope replay, committed
outcome comparison, concurrency, tenant auth, ephemeral loss, streaming build
serialization, and artifact access. They do not prove Linux native execution or
Cloudflare container behavior. Those integration probes belong to the parent.

`worker-configuration.d.ts` is generated locally by Wrangler. Regenerate after
binding changes with `wrangler types --env-interface GeneratedEnv` (the generator
uses a loopback listener). There is no real deploy script or automatic cloud
setup. The parent sets `ADMIN_TOKEN`, `INTERNAL_TOKEN`, `TOKEN_A`, and `TOKEN_B`,
deploys, runs fewer than 1,000 probe requests, and cleans up the experiment.

## Public surface

All responses disable caching. A supplied `X-Experiment-Schema` must equal
`cf-v1`, otherwise the gateway responds 409. Missing/invalid credentials return
401. `TOKEN_A` authenticates Alice and `TOKEN_B` authenticates Bob. The gateway
constructs the actor field; a client-supplied actor cannot change identity.
Native policy controls both writes and snapshots (Alice/alpha, Bob/beta).

| Method/path | Authorization | Body / response |
| --- | --- | --- |
| `GET /health` | None | Schema/mode metadata only; never starts a container |
| `POST /{mode}/command` | Actor | `{requestId,command}` → unwrapped native outcome |
| `POST /{mode}/snapshot` | Actor | `{tenant}` → unwrapped native snapshot |
| `GET /{mode}/status` | Actor | Native sequence/schema, real `bootId`, mode, `journalCount`, `committedCount` |
| `POST /{mode}/admin/destroy` | Admin | Destroys only that container; `{ok:true}` |
| `GET /{mode}/admin/journal` | Admin | `{count}` only; no envelopes or domain data |
| `POST /durable/admin/inject` | Admin | `{point:"after-journal"}` or `{point:"after-native"}` |
| `GET /admin/artifact` | Admin or internal | Streams R2 `cf-native`; 404 if absent |

`{mode}` is exactly `durable` or `ephemeral`. Admin credentials do not grant
actor operations, and actor credentials cannot access build, journal, destroy,
injection, or artifact routes. There is no generic native HTTP proxy.

Command bodies are limited to 16 KiB, request IDs to 1–256 characters, and JSON
nesting to 32 levels. `command` must be an object. Object keys are recursively
sorted; array order and all supplied fields remain significant. JSON numeric
normalization treats `1`/`1.0` and `0`/`-0` alike. The authenticated actor and
request ID form the deduplication key. Reusing it with a different canonical
command returns 409. Native domain failures (`forbidden`, `duplicate`,
`not_found`, `rolled_back`, `invalid`) remain HTTP 200 and consume a sequence.
Transport/malformed input errors use 4xx; native/readiness/replay failures use
503 with a generic code and `Retry-After: 1`.

## Durability and failure injection

The durable DO appends the sequence, actor, request ID, canonical command, and
**exact native envelope string** to SQLite `journal`. A unique constraint scopes
request IDs to actor. It explicitly awaits `storage.sync()` before native I/O.
Only after native returns a valid outcome does it insert the separate `receipts`
row and sync again. SQL triggers prohibit updates/deletes of both tables.
Successes and domain failures are both retained. Neither envelope nor committed
outcome is rewritten.

A promise queue serializes all DO work across external awaits, including reads,
recovery, admin requests, and the lifetime of streamed build execution. The
native HTTP gate provides the second serialization boundary. Native deduplication
uses sequence plus the original envelope bytes.

Before durable reads/commands, the gateway checks native status and reads
`/work/boot-id` through the Node server. This file is created once per container
filesystem, independently of DO memory. A new boot, DO eviction, or regressed
native sequence triggers ordered replay. Every replayed committed result must
match the full stored canonical outcome; mismatch returns 503 and blocks further
operations. Pending envelopes receive a receipt after successful native retry.
Warm requests reuse the verified prefix; replay is paged in batches of 100.
Native state ahead of the durable journal is rejected.

Injection is a persisted, one-shot setting consumed atomically with the next
**new** durable journal entry. Duplicates, conflicts, and reads do not consume it:

- `after-journal`: sync the envelope, return 503 before calling native.
- `after-native`: native commits, return 503 before inserting the DO receipt.

These are deliberately interrupted request windows, not automatic container
destruction. Retry the same request ID, or destroy the container and retry; both
must apply once. A subsequent read also resolves a pending durable command.
Destroy clears bootstrap/replay memory but preserves DO storage and journal.

Ephemeral mode never replays an earlier container boot. Its small DO table holds
boot-scoped idempotency receipts and unresolved transport attempts so a DO-only
eviction does not duplicate an operation in a surviving native database. On a
new filesystem boot those records are discarded, native status supplies the
fresh sequence, and snapshots start empty. Retrying an old request after loss
is a new operation. Ephemeral `journalCount` and `committedCount` stay zero.

## Protected build and bootstrap

All build routes require `ADMIN_TOKEN` and are only available on durable mode:

| Endpoint | Behavior |
| --- | --- |
| `POST /durable/admin/workspace` | Streams gzipped tar to Node `/workspace?dir=/work/repo` |
| `POST /durable/admin/exec` | Forwards `{command,options}` to `/env/exec`, streaming NDJSON |
| `POST /durable/admin/call` | Forwards `{method,args}` to `/env/call` after checking its method allowlist |
| `POST /durable/admin/publish` | Copies/strips `/work/out/cf-native`, streams `/out/raw?path=cf-native` to R2 |

The workspace tar **must have one top-level directory**. The image's unpacker
removes `/work/repo`, then uses `tar -xz --strip-components=1` and creates a local
Git baseline. Supply a trusted archive preserving the LeanDB repository layout;
native's Lake dependency resolves three directories upward. Do not flatten just
the native subdirectory. Build execution should use:

```json
{"command":"lake build cf-native && mkdir -p /work/out && cp .lake/build/bin/cf-native /work/out/cf-native","options":{"cwd":"/work/repo/experiments/cloudflare/native","timeout":1500}}
```

Execution timeout is in **seconds** (default/max 1,500). JSON admin calls have a
1 MiB body limit. An exec stream contains `{output,info}` frames followed by
`{result:{ok:true,value:{exitCode:…}}}` or a result error. HTTP 200 alone does not
mean a build succeeded: inspect the terminal result. Keep consuming the stream;
the DO queue stays held until it finishes or is cancelled. Workspace upload and
other streaming proxy responses hold the queue too.

The call allowlist matches the image's stateless methods: `absolutePath`,
`joinPath`, `readTextFile`, `readTextLines`, `readBinaryFile`, `writeFile`,
`appendFile`, `truncateFile`, `flushFile`, `renameFile`, `fileInfo`, `listDir`,
`canonicalPath`, `exists`, `createDir`, `remove`, `createTempDir`,
`createTempFile`, and `cleanup`. Stateful handles are not exposed. The image's
`$bytes` and error JSON encodings are passed through unchanged.

Publish uses a separate stripped copy and atomic rename, so an existing native
process can keep its executable open. It obtains the output file's size and
uses `FixedLengthStream` for R2's known-length requirement; the Worker never
buffers the binary. The artifact key is always `cf-native`.

Runtime startup preserves a healthy native process. Otherwise it uses the Node
server on port 8080 to run a static bootstrap script: curl the artifact from the
**incoming request URL's origin** with `INTERNAL_TOKEN`, install it in
`/work/out/cf-native`, chmod, and launch via nohup:

```sh
/work/out/cf-native --db /work/state.sqlite serve --http 7411 --bind 0.0.0.0
```

`LEANDB_TOKEN=INTERNAL_TOKEN` is supplied in the process environment, never as
an argv flag. Token values travel in `options.env`; they are not interpolated
into command text. Bootstrap output/errors are consumed internally and never
logged or returned. Native stdout/stderr go to `/work/native.log`. The gateway
has no application logging, and Wrangler observability is disabled.

The native CLI, query wrapper, and argument format were checked against
`../native/{Main,CfNative}.lean`, `LeanDb/Cli.lean`, and `LeanDb/Http.lean`.
Calls are `POST /query/<name>` with `{args:[JSON.stringify(envelope)]}`; status
uses `args:[]`. The gateway unwraps one `{ok:true,result:…}` layer. Fresh native
SQLite needs no separate seed/migration step.

## Experiment limits

- Container inactivity timeout is 30 minutes for build work, 5 minutes for
  runtime. Both containers enable internet access for artifact/toolchain fetches.
  There is no background heartbeat or autonomous restart loop.
- Readiness is bounded: Node startup gets 60 seconds, each health probe 3 seconds;
  bootstrap execution gets 40 seconds plus a 5-second transport allowance (curl
  itself gets 30 seconds); native readiness gets 60 seconds with 2-second probes.
  Replay has a 120-second per-request budget and native operations a 15-second
  timeout. A budget may be exceeded by the final in-flight operation. Retry
  resumes verified progress; it does not replace the journal.
- This is a single serialized stream per mode, with unbounded retained durable
  history, no compaction, snapshots, retention policy, or multi-region protocol.
  It is intended for the supplied experiment of fewer than 1,000 requests.
- All input integers must be JavaScript-safe. Keep resulting counter values and
  snapshot sums safe as well; native supports wider integers. Unsafe native
  command outcomes fail closed instead of committing a rounded DO receipt.
- Admin shell/filesystem access and uploaded tar are trusted. Do not give admin
  access to untrusted users, overwrite native state, or run competing native
  servers. Native status/boot markers cannot detect arbitrary manual corruption
  that preserves sequence and boot identity.
- Publishing replaces one R2 artifact key. Keep the same native semantics while
  exercising a journal: changed replay outcomes deliberately block recovery.
  Container state is disposable; deleting the DO namespace loses the journal.
  Destroying a container does not delete the R2 binary or durable journal.
- No cloud resources, production data, secrets, or deployments were changed by
  local implementation/validation. Live integration and cleanup remain with the
  parent worker.
