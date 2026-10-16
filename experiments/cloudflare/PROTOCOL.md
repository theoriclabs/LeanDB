# Cloudflare experiment protocol v1
Native LeanDB compiled Linux code with SQLite in a Cloudflare Container. Worker routes two modes (durable, ephemeral) to separate Durable Objects/containers. Durable mode journals commands before execution and replays after container loss. Ephemeral mode negative control. Synthetic data only, no production changes. At most two standard-1 containers, under1000 probe requests, cleanup afterwards.

## Native API (private port7411)
POST /query/apply body {"args":["<JSON envelope>"]}. Envelope: {seq:positive integer,actor:"alice"|"bob",requestId:string,command:{type:"create"|"increment"|"rollback",tenant:"alpha"|"beta",key:string,value?:integer,delta?:integer}}.
Native Lean policy alice->alpha, bob->beta for writes AND reads. create inserts unique(tenant,key) counter at value; increment adds delta; rollback adds delta then deliberately fails within transaction.
Native apply returns {ok:boolean,seq:number,code?:string,value?:number}. Domain failures: forbidden, duplicate, not_found, rolled_back, invalid. Native Applied table records seq, exact envelope JSON, result JSON. Same seq+envelope returns identical result; mismatch sequence_conflict. Next new seq must be lastSeq+1 (sequence_gap). Successful mutation+Applied atomic. Failed mutation rolls back first then records failure Applied. Native HTTP gate serializes.
POST /query/snapshot args=[JSON.stringify({actor,tenant})] -> {ok:true,items:[{key,value}],sum:number,count:number} sorted by key; or {ok:false,code:"forbidden"}. POST /query/status args=[] -> {ok:true,lastSeq:number,schemaVersion:"cf-v1"}. Gateway unwraps LeanDB query result if required.
CLI expected cf-native --db /work/state.sqlite serve --http7411 --bind0.0.0.0 (separate flag args); LEANDB_TOKEN env. Native worker must document exact CLI and HTTP response wrapper.

## Public API
Bearer TOKEN_A->alice, TOKEN_B->bob. /health unauthenticated metadata only. X-Experiment-Schema if provided other than cf-v1->409.
POST /{mode}/command {requestId,command}; gateway overrides actor, serializes, assigns seq, canonicalizes command for idempotency (requestId scoped actor). Same ID+command returns original result; different command409. Native domain errors HTTP200 with ok:false. Auth failure401.
POST /{mode}/snapshot {tenant} -> native result directly.
GET /{mode}/status -> {lastSeq,schemaVersion,bootId,journalCount,...}. Durable replay before reads/commands.
Admin POST /{mode}/admin/inject {point:"after-journal"|"after-native"}: next NEW durable command journals then503 before native OR executes native then503 before receipt commit. Retry must apply once.
Admin POST /{mode}/admin/destroy destroys container, clears bootstrap memory, preserves DO journal; returns{ok:true}. GET /{mode}/admin/journal count only.

## Build API (ADMIN_TOKEN only)
POST /durable/admin/workspace forwards gzipped tar to container Node server /workspace?dir=/work/repo.
POST /durable/admin/exec forwards {command,options} to /env/exec (NDJSON).
POST /durable/admin/call forwards {method,args} to /env/call.
POST /durable/admin/publish streams /out/raw?path=cf-native to R2 ARTIFACTS key cf-native.
GET /admin/artifact returns R2 binary (ADMIN_TOKEN or INTERNAL_TOKEN only).
ensureNative starts container Node server8080 default image, probes7411. If absent, curl binary from /admin/artifact with INTERNAL_TOKEN to /work/out/cf-native, chmod, launch via nohup with LEANDB_TOKEN=INTERNAL_TOKEN. Preserve native if already running. Real boot marker in /work/boot-id (not mere DO memory). Health readiness bounded. Inactivity timeout30min build/5min runtime.
