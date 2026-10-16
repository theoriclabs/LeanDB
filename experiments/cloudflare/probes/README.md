# Cloudflare black-box probes

`run.py` is an independent Python 3.10+ standard-library client for
[`../PROTOCOL.md`](../PROTOCOL.md). It uses only the public HTTP API; it does not
import Worker/native code or inspect their storage. No dependencies need installing.

**Do not run live probes until the parent supplies the experiment endpoint and
credentials and explicitly asks for execution.** The runner requires `--execute`
before reading credentials or making requests. This implementation has only been
syntax checked; there are no live results yet.

Use a dedicated synthetic experiment with no other writers. A full run seeds
randomly namespaced counters, destroys the durable container three times and the
ephemeral container once, and leaves the durable journal available for the later
redeploy check. The ephemeral destroy removes all ephemeral state. No resources
are provisioned by this client, but live endpoint requests can start containers
and incur the endpoint's runtime charges. Infrastructure setup, redeployment,
container size/count limits, and final infrastructure cleanup belong to the parent.

Supply the three distinct bearer credentials through `TOKEN_A`, `TOKEN_B`, and
`ADMIN_TOKEN` in the process environment, or through `--tokens-file` pointing to a
private JSON file with exactly those named fields. File mode uses the file alone;
it does not fall back to environment values. Tokens must be nonempty printable
ASCII without whitespace. Do not put literal tokens in command arguments, URLs,
shell history, this directory, or version control. No internal/native token is needed.

Once execution is explicitly authorized, with `BASE_URL` and the credential file
provided by the parent:

```sh
python3 run.py "$BASE_URL" --mode full --execute \
  --tokens-file /secure/path/cf-probe-credentials.json \
  --checkpoint artifacts/experiment.checkpoint.json \
  --evidence artifacts/full.json
```

Omit `--tokens-file` to use the three environment variables. Remote endpoints must
use HTTPS; HTTP is accepted only for `localhost`, `127.0.0.1`, or `::1`. URL userinfo,
query strings, fragments, and whitespace are rejected. Redirects and inherited
proxy settings are disabled so authentication cannot be forwarded to another URL.

The parent then redeploys the Worker independently. Keep the same endpoint,
Durable Object namespace, journal, credentials, and checkpoint, with no intervening
writes. When the parent authorizes the second phase:

```sh
python3 run.py "$BASE_URL" --mode redeploy-check --execute \
  --tokens-file /secure/path/cf-probe-credentials.json \
  --checkpoint artifacts/experiment.checkpoint.json \
  --evidence artifacts/redeploy.json
```

`full` requires a new checkpoint path to prevent accidental reuse of an older
run. It writes intermediate checkpoints with `ready_for_redeploy: false` and
marks the checkpoint ready only after all probes pass. `redeploy-check` rejects
missing, malformed, incomplete, or different-endpoint checkpoints before network
access. It compares the saved snapshots, sequence, and journal count, retries saved
request IDs without adding effects, then forces one further durable-container
destroy and verifies recovery again. It does not perform or independently prove
the external redeploy. A successful check updates the checkpoint's boot marker.
The checkpoint also carries the cumulative request budget into the second phase.
Failed runs invalidate any checkpoint they have loaded or written, preserving the
latest request count and marking it incomplete. Evidence paths must be new and
separate from the checkpoint and credential file.

The full sequence checks:

| Probe | Required observed behavior |
| --- | --- |
| Public health and bootstrap | Health JSON; authenticated status for both actors and both modes; `cf-v1`, integer sequence/journal counts, and nonempty boot markers. |
| Authentication | Missing and invalid bearer credentials receive HTTP 401 for commands, snapshots, and status in both modes; baseline state and sequence remain unchanged. |
| Schema | An incompatible `X-Experiment-Schema` receives HTTP 409 on those routes; `cf-v1` is accepted. |
| Admin protection | Anonymous, Alice, and Bob receive HTTP 401 on both modes' inject/destroy/journal routes, durable workspace/exec/call/publish routes, and `/admin/artifact`. Build routes receive empty payloads; no valid build or exec command is submitted. |
| Create/read/increment | Both tenants can independently use the same key; returned and snapshotted values match the expected mutations. |
| Native tenant contract | Cross-tenant reads and writes return HTTP 200 with `ok:false, code:forbidden`; each rejected write advances the native sequence and journal once and does not change either tenant's counters. |
| Unique constraint and rollback | Duplicate create returns `duplicate`; deliberate rollback returns `rolled_back`; exact snapshots remain unchanged. |
| Derived summary | Every snapshot has unique sorted keys, exact contents, `count == len(items)`, and `sum == sum(item values)`. |
| Idempotency | Same ID/body and reordered JSON keys return the original receipt without state, sequence, or journal changes; changed command under that ID receives HTTP 409. The same ID works independently for Bob. |
| Concurrent increments | Eight workers start together and each performs five increments. Final counter is exactly 40; receipts contain values 1–40, 40 distinct sequences, and exactly 40 new sequence/journal entries. |
| Durable destruction | Snapshots and status are captured before destruction; acknowledgement and changed boot marker are required; both tenants, sequence, journal count, and saved receipts survive. |
| Ephemeral negative control | Both tenants have observed seed data before destruction. A changed boot marker, empty snapshots, zero derived summaries, and reset native sequence are required afterward. Durable contents remain intact. |
| `after-journal` and `after-native` | Each injection's first new command must return HTTP 503 without automatic retry. Retrying that exact request succeeds with one effect, one new sequence and one journal entry; another retry returns the identical receipt. Each case is followed by a destroy, exact recovery, and an additional unchanged receipt retry. |

Limits are fixed in the runner: at most **999 HTTP attempts across a full run and
its checkpoint-linked redeploy checks**,
including failed requests, admin calls, bootstrap attempts, and retries; at most
**eight simultaneous requests**. The budget is checked before every attempt.
Each bootstrap/status recovery and each retrying operation has a **120-second
deadline**, 15-second request timeout, and backoff capped at five seconds. Body
reads tighten the socket timeout to the remaining request time. OS-level DNS and
connect handling is subject to the platform resolver; no successful response
arriving after the operation deadline is accepted. The retry window is per
operation, not a promise that the entire suite completes within two minutes.

Commands retain the same request ID and body across transport failures and
retryable HTTP 408/425/429/500/502/503/504 responses. Every attempt stays in the
evidence. Admin injection/destruction is never automatically retried because an
ambiguous response could otherwise affect a different container or command.
Unexpected assertions stop the sequential suite; concurrent workers already in
flight finish before their results are assessed. Do not blindly rerun a failed
fault-injection stage: an armed injection or applied command can remain on the
server. Inspect the evidence and have the parent re-establish the experiment.

Evidence JSON contains UTC start/end timestamps, monotonic request/run durations,
each HTTP status, parsed response bodies, actual snapshots, assertion expectations
and observations, checkpoint events, failure categories, and request/concurrency
counts (both invocation and cumulative). A pass is computed from responses and state comparisons, never supplied
as a fixture or assumed from an HTTP status alone. Existing data is included in
the baseline and must remain unchanged except for this run's counters.

Only the final outcome, request count, and evidence path are printed. Request
headers, response headers, credentials, and exception messages are never printed
or stored. Parsed evidence and checkpoints redact known credential values
(including JSON-escaped and URL-escaped forms) and sensitive field names before
any write. Unparseable response bodies are omitted, with status/size/error metadata
retained; bodies larger than 256 KiB cannot satisfy JSON assertions. Credentials
remain in memory for authenticated requests. Artifacts are atomically replaced
from private temporary files (mode 0600). Do not treat redaction as permission to
point these probes at production or store unrelated secrets in synthetic state.

| Exit code | Meaning |
| --- | --- |
| `0` | All required assertions for the selected mode passed. |
| `1` | An observed API/state assertion failed, including post-bootstrap recovery or retry exhaustion. |
| `2` | Setup error: missing execution opt-in, unusable credentials/URL/checkpoint/output paths, or initial readiness unavailable within its deadline. |
| `3` | Runner failure, exhausted request budget, or inability to persist evidence. |
| `130` | Interrupted; available observations are saved when ordinary exception handling can finish. |

An HTTP 200 response with a malformed protocol body is an assertion failure, even
during bootstrap. A failure is not a pass for the remaining skipped checks. A
checkpoint is suitable for redeploy verification only when its originating run
has passing evidence and `ready_for_redeploy` is true. A setup error generally
also writes evidence; missing `--execute` deliberately does not read credentials
or create artifacts. If an output path conflicts with existing evidence or a
credential/checkpoint path, setup evidence goes to a fresh `artifacts/` filename.

Interpretation limits: this is a finite, small synthetic workload. Successful
results establish the public contract observed at that endpoint during this run;
they do not prove general throughput, crash safety for every instruction boundary,
multi-region behavior, long-term durability, or absence of implementation defects.
HTTP 200 native-shaped domain rejections and native sequence receipts exercise the
specified native-policy contract, but a black-box client cannot prove that policy
or uniqueness was enforced inside Lean/SQLite rather than imitated by a gateway.
Likewise, admin destroy acknowledgements and changed boot markers are the protocol's
evidence of replacement; this client cannot independently attest process identity,
image contents, journal storage, or the point at which a 503 was injected. The
ephemeral control and post-destroy receipt checks strengthen the comparison but
do not remove those limits. Independent build/infra evidence belongs to the parent.

For a local syntax-only check that reads no credentials and makes no requests:

```sh
python3 -W error -c 'import ast, pathlib; p = pathlib.Path("run.py"); ast.parse(p.read_text(), filename=str(p)); print("Syntax OK")'
```

The client leaves synthetic durable counters and the journal intact because the
protocol supplies no row-delete/reset API and redeploy verification needs them.
Destroying a container is not infrastructure cleanup. After preserving both runs'
evidence, the parent is responsible for its authorized experiment cleanup.
