# LeanDB on Cloudflare: executable feasibility experiment

Date: 2026-10-09. Source baseline: LeanDB 0.5.0, commit 8920c70.
Question: Can native LeanDB serve correct domain operations within Cloudflare, including after its Linux container disappears?

## Hypotheses and decision rules

| Hypothesis | Intervention | Required observation |
|---|---|---|
| Native hosting works | Build pinned Lean source on a Cloudflare Linux container; expose through Worker | Native executable serves actual SQLite-backed LeanDB operations |
| Domain correctness remains in Lean | Invoke tenant-scoped commands, duplicate keys and deliberate transaction failure | Unauthorized calls and duplicate rows rejected; failed transaction leaves no partial mutation |
| Single writer handles concurrent clients | Eight clients send increments | Final value and derived sum equal acknowledged increments exactly |
| Retries are safe | Retry same request; reuse ID with changed command | Original outcome reused with no second effect; conflicting reuse rejected |
| Raw container disk is insufficient | Destroy ephemeral control container and bootstrap again | State disappears (expected negative result) |
| Durable journal recovers domain state | Destroy durable container, replay into new native DB | Exact pre-destruction state and acknowledged outcomes recovered |
| Crash windows are recoverable | Fail after journal append and after native commit before receipt commit | Retried command applies exactly once; state remains correct after another destruction |
| Worker rollout preserves service state | Redeploy same worker implementation | Durable snapshot persists; no lost acknowledgements |

## Architecture and scope

Public HTTPS -> Worker authentication -> per-mode Durable Object serialization -> native LeanDB HTTP -> SQLite container file.
Durable mode adds an append-only DO storage command journal and durable receipts. The Lean program owns tenant policy, constraints, transactions and derived values. R2 stores only the compiled executable, not live SQLite. Code/schema version is fixed for replay. Ephemeral mode omits replay and is a deliberate negative control.

This investigates a journal-backed native architecture. It does not claim SQLite's container file itself is durable, native SQLite can open a D1/DO database, or Lean executes directly inside a Worker isolate. It does not establish production readiness, arbitrary LeanDB program replay safety, schema upgrades, multi-region failover, high load, long outages, malicious-client security, or a production identity provider.

## Execution and evidence

Three isolated terminal agents implement native fixture, gateway and independent probes. Parent integrates, deploys temporary resources, checks actual receipts and evidence, and cleans up.
Record pinned source/image, build output and binary digest; black-box assertions and request latencies; before/after snapshots; resource IDs; deploy versions; cleanup output. Never store credentials in repository evidence.
The fixture exposes only synthetic counters for alpha/alice and beta/bob. Admin build/fault endpoints are temporary and protected with a separate random token.

## Bounds

New resources only: leandb-cf-exp-20261009 Worker/container application and R2 bucket. No changes to wybe-runtime.
At most two standard-1 containers simultaneously. Fewer than 1000 probe requests. No billing changes or new subscription. Build remotely to avoid a large local toolchain download on a nearly full disk. Destroy temporary containers and remove temporary cloud resources at conclusion. Resource usage recorded from elapsed time is an estimate; no invoice claim.

## Sources

- Cloudflare Containers API: https://developers.cloudflare.com/containers/api/durable-object-container/
- Container disk/lifecycle FAQ: https://developers.cloudflare.com/containers/faq/
- Image management: https://developers.cloudflare.com/containers/guides/image-management/
- Pricing: https://developers.cloudflare.com/containers/platform/pricing/
