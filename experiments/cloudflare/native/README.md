# Native Cloudflare fixture

Implements `../PROTOCOL.md` using `import LeanDb`, native LeanDB transactions,
and a real SQLite database. All code belongs to this directory. LeanDB resolves
from `../../..`; preserve that repository layout in the Linux build workspace.

## Build and start (Linux builder)

The declared required toolchain is `leanprover/lean4:v4.33.0`. A parent-provided
isolated fixture was compiled locally using installed Lean4, and its binary
passed the local macOS smoke test described below. Its `CfNative.lean` source
differs from the current file, so that result does not validate this exact
source revision. Linux compilation and execution remain pending. Run on the
parent-managed Linux builder with the declared toolchain installed:

```sh
cd /work/repo/experiments/cloudflare/native
lake build cf-native
mkdir -p /work/out
cp .lake/build/bin/cf-native /work/out/cf-native
```

Exact startup command, with **separate flag arguments**:

```sh
/work/out/cf-native --db /work/state.sqlite serve --http 7411 --bind 0.0.0.0
```

The launcher must supply nonempty `LEANDB_TOKEN` in the process environment
(the gateway's `INTERNAL_TOKEN`). Do not print it or put it in argv. A fresh
database initializes on open; no seed or migration command is required. Restart
against the same path preserves data and receipts. Each mode needs its own
container/database. Keep one native server per database. Runtime readiness:
`GET http://127.0.0.1:7411/healthz`, followed by an authenticated status query to
check the schema/session. The health response alone does not verify schema.

## Gateway contract

All three calls use `POST /query/<name>`, `Content-Type: application/json`, and
`Authorization: Bearer <INTERNAL_TOKEN>`. LeanDB's HTTP dispatch gate serializes
the whole query, including mutation rollback and receipt storage.

| Query | JSON request body |
| --- | --- |
| `apply` | `{"args":["<exact JSON envelope string>"]}` |
| `snapshot` | `{"args":["{\"actor\":\"alice\",\"tenant\":\"alpha\"}"]}` |
| `status` | `{"args":[]}` |

The fixture explicitly wraps every named-query result using `Cli.okResult`:

```json
{"ok":true,"result":{"ok":true,"seq":1,"value":10}}
{"ok":true,"result":{"ok":false,"seq":2,"code":"duplicate"}}
{"ok":true,"result":{"ok":true,"items":[{"key":"k","value":10}],"sum":10,"count":1}}
{"ok":true,"result":{"ok":true,"lastSeq":2,"schemaVersion":"cf-v1"}}
```

These are HTTP 200, including domain failures. Unwrap **one level**, returning
`body.result` when outer `body.ok === true` and the `result` property exists.
Outer `ok:false` or non-200 is a transport/engine failure, not an Applied domain
receipt; do not acknowledge it as journal completion. Token failures are HTTP
401. Generic table verbs are disabled (HTTP 403); this private service still
exposes LeanDB operator routes, which the public gateway must not proxy.

## Semantics and boundary decisions

- Alice can read/write alpha; Bob can read/write beta. Cross-tenant operations
  return `forbidden` before reading or mutating the counter. Actor identity is
  trusted only from the authenticated internal gateway.
- `Counter` has a real SQLite UNIQUE index over `(tenant,key)`. `Applied` has a
  real UNIQUE index over `seq`. Concrete `Entity.specs` preserve these indexes
  through the type-erased CLI table descriptor.
- New sequences must be `lastSeq + 1`, starting at 1. An existing sequence with
  the identical argument string returns its stored result. Any byte difference,
  including whitespace or object field order, returns `sequence_conflict`.
  An unused non-next sequence returns `sequence_gap`. Neither consumes a seq.
- An outer `BEGIN IMMEDIATE` holds the sequence check, mutation, and receipt
  through commit. An inner native transaction uses a SQLite savepoint. Domain
  aborts roll that savepoint back **before** the failure receipt is inserted.
  `rollback` performs the update then aborts with `rolled_back`; it leaves the
  original value intact while consuming its sequence. Successful writes and
  receipts commit atomically. Engine/IO errors propagate and consume no seq.
- Receipts store the exact envelope string and compressed result JSON. Results
  are parsed from storage on retry. Requests with a usable next sequence but an
  invalid command also receive a durable `invalid` receipt. Malformed JSON or an
  invalid/missing sequence cannot get a receipt (`seq:0` when unavailable).
- `create` requires integer `value`; `increment` and `rollback` require integer
  `delta`. The optional fields in the protocol are interpreted per command;
  there are no implicit defaults. Any supplied `value`/`delta` must be integer.
  Unknown actors, tenants, command types, missing string fields, or missing
  operands yield `invalid`. `requestId` and `key` may be any JSON string.
- SQLite values/operands/sequences are signed 64-bit integers; seq must be
  positive. Arithmetic is checked before conversion, so overflow is `invalid`,
  never wraparound. Snapshot sums use Lean `Int`. For exact JavaScript arithmetic,
  the gateway/probes should use safe integers (including sums).
- Native deduplication is by sequence and exact envelope. Actor-scoped
  `requestId` deduplication/canonicalization belongs to the gateway. It must
  preserve the original native envelope string for retries and durable replay.
- Snapshot items are sorted by key, filtered by the checked tenant, with an
  empty result of `items:[],sum:0,count:0`. Status includes successful and failed
  Applied sequences. Boot markers and the durable command journal are external.

## Smoke and integration validation

Against an already-built binary, run the standard-library-only smoke test:

```sh
python3 smoke.py .lake/build/bin/cf-native
```

It launches isolated localhost servers with a synthetic test token and new
temporary SQLite paths. It checks HTTP wrapping/auth, policy, composite UNIQUE
DDL, create/increment, rollback persistence, all domain codes, exact duplicate
replay and conflicts, gaps, sorted snapshots, stored envelope/result receipts,
concurrent retries, process restart, and full replay into a fresh database.
Process shutdown uses `terminate()` (SIGTERM on macOS/Linux), with `kill()` only
if the process has not exited after five seconds. The test does not report which
shutdown branch ran and does not establish abrupt-kill or in-flight crash safety.
It prints its temporary directory for inspection and retains it. It does not
build, download a toolchain, deploy, or contact the cloud.

Parent gateway/probes should additionally verify both injected crash windows:
`after-journal` and `after-native`, then retry the same request ID and inspect
snapshot/status. Destroy/recreate durable mode and verify ordered replay restores
state and failures; repeat for ephemeral mode and verify state loss. Also check
actor-scoped request-ID conflicts, public auth, and schema-header rejection.
Native request replay must use the original envelope bytes in all cases.

LOCAL macOS validation was independently run on 2026-10-09 using macOS 15.5
arm64 and the parent-provided Mach-O arm64 binary at
`/private/tmp/leandb-cf-20261009/local-src/experiments/cloudflare/native/.lake/build/bin/cf-native`.
`smoke.py` exited **0**, with empty stderr and the result:

```text
PASS: native fixture smoke; 12 persisted/replayed receipts
```

[Local validation evidence](../evidence/native-local.json) records the exact
command, timestamps, stdout/stderr, binary SHA-256, smoke script SHA-256, and
source comparisons. `Main.lean` matches the isolated build source byte-for-byte;
`CfNative.lean` does **not** match, differing in two error-handling blocks in
`mutate`. Both source copies and the binary were unchanged during validation.
The initial passing result applies to that supplied binary. The parent then
rebuilt the final source and repeated the smoke successfully; both source hashes
match exactly in [final-source validation](../evidence/native-local-current.json).
The earlier mismatch is retained as diagnostic evidence.

The smoke's SQLite databases and server logs are retained under
`.smoke-artifacts/`; the exact run directory is recorded in the evidence.
The Linux build and cloud/gateway integration subsequently passed. See the
[experiment report](../README.md) for live correctness, crash-window and recovery
results, including the measured cold-start delays. The direct native smoke ran
on macOS; Linux behavior was exercised through the live gateway probes.
