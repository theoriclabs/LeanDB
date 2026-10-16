# LeanDB on Cloudflare: experiment results

**2026-10-09 — Native hosting is feasible with an explicit durable recovery layer.**

The tested architecture ran real compiled LeanDB and SQLite inside Cloudflare Containers, behind a Worker and a SQLite Durable Object. A durable command journal restored the native database after container replacement. The control configuration, which relied on the container filesystem, lost its data.

Correctness checks passed. This prototype has substantial request overhead and occasional long cold recoveries, so the result supports further engineering rather than a production readiness claim.

## What ran

~~~mermaid
flowchart LR
    C[HTTPS clients] --> W[Worker authentication]
    W --> D[Durable Object: ordered journal and receipts]
    D --> L[Container: compiled LeanDB domain]
    L --> S[(Ephemeral SQLite file)]
    R[(R2: compiled executable)] --> L
    D -. replay after replacement .-> L
~~~

LeanDB owns the fixture's tenant policy, unique constraint, counter transitions, transaction rollback and derived summaries. The gateway owns authentication, serialization, request deduplication and durable command storage. R2 holds the executable; it does not hold the live SQLite database.

The negative control uses a separate object/container and omits durable replay. Both modes use the same native program. Six durable container replacements and one control replacement were exercised, in addition to a Worker redeploy.

- LeanDB: 8920c70b1c01e2d0109e83dbc1be14adbf05ed96 / 0.5.0.
- Compiler: Lean 4.33.0, Linux x86_64.
- Cloud build: **441 seconds**, excluding toolchain setup.
- Stripped executable: **84,161,720 bytes**; SHA-256 d4a2aca0f20525696bbc8d46d6f95e788d83832edcace75382e80897a37edcca.
- Two standard-1 containers maximum: 0.5 vCPU, 4 GiB memory, 8 GB disk each.
- Six terminal worker tasks implemented and validated the fixture, gateway and probes. Their [receipts](evidence/terminal-workers.json) are retained.
- Billing cost was not independently measured; no production cost estimate is claimed.
- All test data was synthetic. The build reused an existing immutable container image; it did not alter the Wybe application.

## Correctness results

**302 live HTTP probe requests; 1,387 assertions passed; zero failed assertions.** Assertions include response-shape and state checks, so this is not a count of independent test scenarios. There were expected injected failures and transient recovery errors.

| Check | Observed result |
| --- | --- |
| Native hosting | Built and served the real LeanDB executable in Cloudflare; final restored executable matched the build hash |
| Authentication and schema guard | Missing/invalid tokens rejected; incorrect schema header returned 409 |
| Tenant isolation | Lean rejected cross-tenant reads and writes; client-supplied actor could not change identity |
| Uniqueness and transactions | Duplicate composite key rejected; deliberate write-then-abort left state unchanged |
| Derived state | Counts and sums matched the independent client model |
| Concurrent clients | Eight clients produced exactly 40 increments and 40 distinct sequences |
| Request retries | Duplicate requests returned stable outcomes without another effect; conflicting ID reuse returned 409 |
| Raw filesystem control | Values 31 and 41 disappeared after replacement; both tenant snapshots became empty |
| Durable recovery | State and receipts survived all six tested replacements |
| Worker redeploy | State and receipts persisted; the native container stayed up, then passed another forced replacement |
| Interrupted commit windows | After-journal and after-native failures recovered exactly once, including destruction **before** the first retry |

The final full-run checkpoint contained Alice's values 40 and 42 (sum 82), and Bob's value 22. The extra crash probes then added a counter and verified successive values 7 and 12 after destructive recovery.

Evidence:

- [Full cloud run](evidence/cloud-full.json): 248 requests, 1,181 assertions.
- [Redeploy check](evidence/cloud-redeploy.json): 32 requests, 188 assertions.
- [Destroy before retry](evidence/cloud-crash-before-retry.json): 22 requests, 18 assertions.
- [Cloud build and provenance](evidence/cloud-build.json), [complete build log](evidence/cloud-build.log), [restored binary hash](evidence/runtime-binary-final.ndjson).
- [Final-source local native smoke](evidence/native-local-current.json): 12 persisted/replayed receipts.
- [Gateway local tests](evidence/gateway-local-tests.txt): 28 passed, plus successful TypeScript check and deployment dry run.

## Latency and availability

These are client-observed measurements from one small run, including network/TLS, repeated gateway readiness checks, queueing and native execution. No latency SLO was specified in advance.

| Measurement | Observed |
| --- | --- |
| Initial native startup | 5.52 s in the existing builder container; 4.93 s in a fresh control container |
| Sequential command responses | p50 **607 ms**, p95 **701 ms**, 11 requests |
| Eight-client increment responses | p50 **4.16 s**, p95 **4.52 s**, 40 increments |
| Four recovery checks through verified snapshots | **8.52–12.42 s** |
| Ephemeral cold recovery outlier | **74.41 s**, including three 15-second client timeouts |
| Destroy-before-retry after-journal outlier | Approximately **70.59 s**, including a **61.79 s container_ready_timeout** |
| Destroy-before-retry after-native recovery | Approximately **10.29 s** |

The last two estimates sum recorded request durations and retry waits. The extra runner did not record per-request wall timestamps. See [measurement summary](evidence/summary.json) and raw request evidence.

All recoveries succeeded within the configured retry windows. Startup was not consistently fast. The timeout identifies failure to obtain container-server readiness within the wrapper's deadline; this run did not isolate the underlying cause.

The wrapper performs health, boot-marker and status requests before domain calls, and downloads an 84 MB executable after filesystem loss. A purpose-built image containing the executable and a smaller warm request path are concrete optimization targets. These measurements do not isolate LeanDB's execution time.

## Scope and remaining work

This supports **Worker + Durable Object journal + native LeanDB container** as a viable hosting route for deterministic domain state transitions. Successful command responses in durable mode are backed by durable journal/receipt writes, and the native SQLite file can be reconstructed.

It does not establish direct Lean execution in a Worker isolate, a D1 backend, compatibility of SQLite WAL with an R2 mount, or correctness of every LeanDB API. The fixture uses the native DbM/Entity API; the portable LeanDb.Model interpreter path was not exercised.

Before production use:

1. **Bound recovery work.** This experiment retains and replays the entire journal. It has no compaction, snapshot policy, independent backup/restore procedure or large-history benchmark. The fixture also scans tables.
2. **Version replay semantics.** Pin executable/schema versions to journal segments. Keep external effects outside replay, or persist their results and use effect-specific idempotency. A recorded command can execute during recovery even when its caller received a 503.
3. **Improve availability and latency.** Investigate the 70–74 second outliers, reduce readiness round trips, and test a packaged native image under realistic load and placement.
4. **Finish the transport and identity contract.** This fixture uses two synthetic bearer identities. JavaScript-safe input integers do not guarantee safe cumulative results; an oversized native result currently fails closed and can leave the journal pending. Production needs an exact integer encoding or explicit domain bounds.
5. **Test operational failures.** Regional failures, long outages, schema upgrades, code rollbacks, production identity integration and sustained load remain untested.

Cloudflare documents container filesystem loss and the Durable Object/container control APIs: [Containers FAQ](https://developers.cloudflare.com/containers/faq/), [Durable Object Container API](https://developers.cloudflare.com/containers/api/durable-object-container/). This experiment measured the journal approach; container snapshots and other persistence designs were not compared.

## Reproduce and review

- [Plan and acceptance criteria](PLAN.md)
- [Wire protocol](PROTOCOL.md)
- [Runbook](RUNBOOK.md)
- [Native fixture](native/README.md)
- [Gateway](gateway/README.md)
- [Independent probes](probes/README.md)

An early local validation found a source/binary mismatch caused by a concurrent final source edit. The final source was rebuilt and passed; both the initial diagnostic and corrected evidence are retained. The cloud source and final restored executable hashes matched. The extra crash test used a redirect-blocking runtime guard; that same guard is now included in its script.

## Cleanup

**Cleanup completed and verified.** The temporary Worker, Durable Object namespace, container application, R2 object and bucket are absent. The existing Wybe container application remains. The shared image was retained. See [resource status](evidence/resources.json) and the cleanup receipts in evidence/.
