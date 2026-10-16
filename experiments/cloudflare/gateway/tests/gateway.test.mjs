import assert from "node:assert/strict";
import { DatabaseSync } from "node:sqlite";
import { spawnSync } from "node:child_process";
import test from "node:test";
import { build } from "esbuild";

// Execute the actual Worker/DO code with real SQLite and deterministic network
// doubles. No Cloudflare credentials, Docker, ports, or cloud calls are needed.
const bundled = await build({
  stdin: { contents: 'export { default } from "./src/index.ts"; export * from "./src/index.ts"; export * from "./src/protocol.ts"; export * from "./src/container.ts";', resolveDir: process.cwd(), loader: "ts" },
  bundle: true, format: "esm", platform: "node", write: false,
  plugins: [{ name: "worker-base", setup(build) {
    build.onResolve({ filter: /^cloudflare:workers$/ }, () => ({ path: "base", namespace: "test" }));
    build.onLoad({ filter: /.*/, namespace: "test" }, () => ({ contents: "export class DurableObject { constructor(ctx, env) { this.ctx = ctx; this.env = env; } }" }));
  } }],
});
const { default: worker, LeanDbHost, NativeContainer, canonical, BOOTSTRAP } = await import(`data:text/javascript;base64,${Buffer.from(bundled.outputFiles[0].text).toString("base64")}`);

globalThis.FixedLengthStream = class extends TransformStream {
  constructor(length) {
    let seen = 0;
    super({ transform(chunk, controller) { seen += chunk.byteLength; controller.enqueue(chunk); }, flush() { assert.equal(seen, length); } });
  }
};
const delay = ms => new Promise(resolve => setTimeout(resolve, ms));
const ok = value => Response.json({ ok: true, result: value });
const frame = value => `${JSON.stringify(value)}\n`;
const execDone = () => new Response(frame({ output: "" }) + frame({ result: { ok: true, value: { exitCode: 0 } } }), { headers: { "content-type": "application/x-ndjson" } });

class Storage {
  db = new DatabaseSync(":memory:");
  synced = 0;
  events = [];
  constructor() {
    this.db.exec("PRAGMA foreign_keys = ON");
    this.sql = { exec: (sql, ...args) => {
      if (sql.includes("CREATE TABLE")) { this.db.exec(sql); return this.cursor([]); }
      const rows = this.db.prepare(sql).all(...args);
      this.events.push(sql);
      return this.cursor(rows);
    } };
  }
  cursor(rows) { return { toArray: () => rows, one: () => { assert.equal(rows.length, 1); return rows[0]; } }; }
  transactionSync(action) {
    this.db.exec("BEGIN");
    try { const result = action(); this.db.exec("COMMIT"); return result; }
    catch (error) { this.db.exec("ROLLBACK"); throw error; }
  }
  async sync() {
    this.synced = this.db.prepare("SELECT COUNT(*) AS n FROM journal").get().n;
    this.events.push("SYNC");
    await delay(1);
  }
}

class Container {
  running = false;
  nativeReady = false;
  bootId;
  starts = [];
  timeouts = [];
  execs = [];
  calls = [];
  applied = new Map();
  counters = new Map();
  applyCalls = [];
  active = 0;
  maxActive = 0;
  loseReply = false;
  alterOutcome = false;
  bootFailure = false;
  execResponse;
  artifact = new Uint8Array([127, 69, 76, 70, 1, 2, 3, 4]);
  constructor(storage) { this.storage = storage; }
  start(options) { this.running = true; this.starts.push(options); }
  async setInactivityTimeout(ms) { this.timeouts.push(ms); }
  async destroy() {
    this.running = false; this.nativeReady = false; this.bootId = undefined;
    this.applied.clear(); this.counters.clear();
  }
  getTcpPort(port) { return { fetch: (url, init) => port === 8080 ? this.node(url, init) : this.native(url, init) }; }
  async node(url, init) {
    assert.equal(this.running, true);
    const parsed = new URL(url);
    if (parsed.pathname === "/health") return Response.json({ ok: true, protocol: 4 });
    if (parsed.pathname === "/workspace") { this.workspace = { url, body: init.body }; return Response.json({ ok: true, baseline: "test-baseline" }); }
    if (parsed.pathname === "/out/raw") { assert.equal(parsed.searchParams.get("path"), "cf-native"); return new Response(this.artifact); }
    const body = JSON.parse(init.body);
    if (parsed.pathname === "/env/call") {
      this.calls.push(body);
      if (body.method === "readTextFile" && body.args[0] === "/work/boot-id") {
        return Response.json(this.bootId ? { ok: true, value: this.bootId } : { ok: false, error: { $fileError: { code: "not_found" } } });
      }
      if (body.method === "fileInfo") return Response.json({ ok: true, value: { size: this.artifact.length } });
      return Response.json({ ok: true, value: "test-file" });
    }
    assert.equal(parsed.pathname, "/env/exec");
    this.execs.push(body);
    if (body.command.includes("/work/boot-id")) this.bootId ??= body.command.match(/[0-9a-f-]{36}/)[0];
    else if (body.command === BOOTSTRAP) {
      if (this.bootFailure) return new Response(frame({ output: "private bootstrap diagnostic" }) + frame({ result: { ok: true, value: { exitCode: 22 } } }));
      this.nativeReady = true;
    } else if (this.execResponse) return this.execResponse;
    return execDone();
  }
  async native(url, init) {
    if (!this.nativeReady) throw new Error("not listening");
    assert.equal(init.headers.authorization, "Bearer test-internal");
    this.active++;
    this.maxActive = Math.max(this.maxActive, this.active);
    try {
      await delay(1);
      const query = new URL(url).pathname.split("/").at(-1);
      const { args } = JSON.parse(init.body);
      if (query === "status") return ok({ ok: true, lastSeq: this.applied.size, schemaVersion: "cf-v1" });
      if (query === "snapshot") {
        const { actor, tenant } = JSON.parse(args[0]);
        if (!this.allowed(actor, tenant)) return ok({ ok: false, code: "forbidden" });
        const items = [...this.counters].filter(([key]) => key.startsWith(`${tenant}:`)).map(([key, value]) => ({ key: key.slice(tenant.length + 1), value })).sort((a, b) => a.key.localeCompare(b.key));
        return ok({ ok: true, items, sum: items.reduce((n, item) => n + item.value, 0), count: items.length });
      }
      assert.equal(query, "apply");
      const raw = args[0], env = JSON.parse(raw), { seq, command: c } = env;
      this.applyCalls.push(raw);
      const isDurable = this.storage.db.prepare("SELECT value FROM control WHERE key = 'mode'").get()?.value === "durable";
      if (isDurable) assert.ok(this.storage.synced >= seq, "journal must be synced BEFORE native mutation");
      const prior = this.applied.get(seq);
      if (prior) return ok(prior.raw === raw ? prior.result : { ok: false, seq, code: "sequence_conflict" });
      if (seq !== this.applied.size + 1) return ok({ ok: false, seq, code: "sequence_gap" });
      const key = `${c.tenant}:${c.key}`;
      let result;
      const reject = code => ({ ok: false, seq, code });
      if (!["create", "increment", "rollback"].includes(c.type) || !Number.isInteger(c.type === "create" ? c.value : c.delta)) result = reject("invalid");
      else if (!this.allowed(env.actor, c.tenant)) result = reject("forbidden");
      else if (c.type === "create" && this.counters.has(key)) result = reject("duplicate");
      else if (c.type !== "create" && !this.counters.has(key)) result = reject("not_found");
      else if (c.type === "rollback") result = reject("rolled_back");
      else {
        const value = c.type === "create" ? c.value : this.counters.get(key) + c.delta;
        this.counters.set(key, value);
        result = { ok: true, seq, value };
      }
      if (this.alterOutcome) result = { ...result, value: 9876 };
      this.applied.set(seq, { raw, result });
      if (this.loseReply) { this.loseReply = false; throw new Error("reply lost after native commit"); }
      return ok(result);
    } finally { this.active--; }
  }
  allowed(actor, tenant) { return actor === "alice" && tenant === "alpha" || actor === "bob" && tenant === "beta"; }
}

function harness() {
  const hosts = new Map(), r2 = new Map(), writes = [];
  const env = {
    ADMIN_TOKEN: "test-admin", INTERNAL_TOKEN: "test-internal", TOKEN_A: "test-alice", TOKEN_B: "test-bob",
    HOSTS: { idFromName: name => name, get: name => {
      if (!hosts.has(name)) {
        const storage = new Storage(), container = new Container(storage);
        const ctx = { storage, container, waitUntil(promise) { promise.catch(() => {}); } };
        hosts.set(name, { ctx, host: new LeanDbHost(ctx, env) });
      }
      return hosts.get(name).host;
    } },
    ARTIFACTS: {
      async put(key, body) {
        assert.ok(body instanceof ReadableStream, "publish must stream");
        writes.push(key);
        const bytes = new Uint8Array(await new Response(body).arrayBuffer());
        r2.set(key, bytes);
        return { size: bytes.length, httpEtag: '"test-etag"' };
      },
      async get(key) {
        const bytes = r2.get(key);
        return bytes ? { body: new Response(bytes).body, size: bytes.length, httpEtag: '"test-etag"' } : null;
      },
    },
  };
  const fetch = (path, body, token = "test-alice", method = body === undefined ? "GET" : "POST", headers = {}) => worker.fetch(new Request(`https://experiment.example${path}`, {
    method, headers: { ...(token ? { authorization: `Bearer ${token}` } : {}), "content-type": "application/json", ...headers },
    ...(body === undefined ? {} : { body: JSON.stringify(body) }),
  }), env);
  const call = async (...args) => { const response = await fetch(...args); return { status: response.status, body: await response.json() }; };
  const state = (mode = "durable") => hosts.get(`cf-v1:${mode}`);
  const restart = (mode = "durable") => { const s = state(mode); s.host = new LeanDbHost(s.ctx, env); };
  return { env, fetch, call, state, restart, hosts, r2, writes };
}
const create = (requestId = "create", tenant = "alpha", value = 10) => ({ requestId, command: { type: "create", tenant, key: "k", value } });
const change = (requestId, type = "increment", delta = 2) => ({ requestId, command: { type, tenant: "alpha", key: "k", delta } });
const send = (h, body, mode = "durable", token = "test-alice") => h.call(`/${mode}/command`, body, token);
const admin = (h, action, body = {}, mode = "durable") => h.call(`/${mode}/admin/${action}`, body, "test-admin");
const snapshot = (h, mode = "durable") => h.call(`/${mode}/snapshot`, { tenant: "alpha" });

test("health is metadata-only; auth/schema/method failures do not start containers", async () => {
  const h = harness();
  assert.equal((await h.call("/health", undefined, null)).status, 200);
  assert.equal((await h.call("/durable/status", undefined, null)).status, 401);
  assert.equal((await h.call("/durable/status", undefined, "test-admin")).status, 401);
  assert.equal((await h.call("/durable/admin/journal", undefined, "test-alice")).status, 401);
  assert.equal((await h.call("/admin/artifact", undefined, "test-alice")).status, 401);
  assert.equal((await h.call("/durable/status", undefined, "test-alice", "GET", { "x-experiment-schema": "wrong" })).status, 409);
  assert.equal(h.hosts.size, 0);
  assert.equal((await h.call("/durable/status", {}, "test-alice")).status, 405);
  assert.equal(h.state().ctx.container.starts.length, 0);
});

test("canonical idempotency, actor override, actor scope, and native domain failures", async () => {
  const h = harness();
  const first = await send(h, { ...create("id"), actor: "bob" });
  assert.deepEqual(first, { status: 200, body: { ok: true, seq: 1, value: 10 } });
  assert.deepEqual(await send(h, { requestId: "id", command: { value: 10, key: "k", tenant: "alpha", type: "create" } }), first);
  assert.equal((await send(h, create("id", "alpha", 20))).status, 409);
  assert.equal((await send(h, create("id", "beta", 7), "durable", "test-bob")).body.seq, 2);
  assert.equal((await send(h, create("forbidden", "beta"))).body.code, "forbidden");
  assert.equal((await h.call("/durable/snapshot", { tenant: "beta", actor: "bob" })).body.code, "forbidden");
  assert.equal((await send(h, create("duplicate"))).body.code, "duplicate");
  assert.equal((await send(h, { requestId: "invalid", command: { type: "bogus" } })).body.code, "invalid");
  assert.equal((await send(h, { requestId: "missing", command: { type: "increment", tenant: "alpha", key: "no", delta: 1 } })).body.code, "not_found");
  assert.equal((await send(h, change("rollback", "rollback", 999))).body.code, "rolled_back");
  assert.equal((await snapshot(h)).body.sum, 10);
  assert.deepEqual((await h.call("/durable/admin/journal", undefined, "test-admin")).body, { count: 7 });
});

for (const point of ["after-journal", "after-native"]) {
  for (const destroy of [false, true]) {
    test(`${point}: retry exactly once after ${destroy ? "container destruction" : "DO eviction with warm container"}`, async () => {
      const h = harness();
      await send(h, create());
      await admin(h, "inject", { point });
      const crashed = await send(h, change("change"));
      assert.equal(crashed.status, 503);
      const { storage, container } = h.state().ctx;
      assert.equal(storage.db.prepare("SELECT COUNT(*) AS n FROM journal").get().n, 2);
      assert.equal(storage.db.prepare("SELECT COUNT(*) AS n FROM receipts").get().n, 1);
      assert.equal(container.applied.size, point === "after-native" ? 2 : 1);
      if (destroy) await admin(h, "destroy");
      h.restart();
      assert.deepEqual(await send(h, change("change")), { status: 200, body: { ok: true, seq: 2, value: 12 } });
      assert.equal((await snapshot(h)).body.sum, 12);
      assert.equal((await send(h, change("change"))).body.value, 12);
      assert.equal((await h.call("/durable/status")).body.journalCount, 2);
    });
  }
}

test("injection survives DO eviction and is consumed only by a new command", async () => {
  const h = harness();
  await send(h, create());
  await admin(h, "inject", { point: "after-journal" });
  h.restart();
  assert.equal((await send(h, create())).status, 200);
  assert.equal((await send(h, create("create", "alpha", 99))).status, 409);
  assert.equal((await snapshot(h)).status, 200);
  assert.equal((await send(h, change("new"))).status, 503);
  // A read also repairs the pending command before exposing domain state.
  assert.equal((await snapshot(h)).body.sum, 12);
  assert.equal((await send(h, change("next"))).status, 200);
});

test("full replay restores ordered successes and failures with byte-identical envelopes", async () => {
  const h = harness();
  await send(h, create());
  await send(h, change("increment", "increment", 5));
  await send(h, change("rollback", "rollback", 200));
  await send(h, create("duplicate"));
  await send(h, create("forbidden", "beta"));
  const before = await h.call("/durable/status");
  const exact = h.state().ctx.storage.db.prepare("SELECT envelope FROM journal ORDER BY seq").all().map(r => r.envelope);
  await admin(h, "destroy");
  assert.equal((await h.call("/durable/admin/journal", undefined, "test-admin")).body.count, 5);
  assert.equal((await snapshot(h)).body.sum, 15);
  const after = await h.call("/durable/status");
  assert.notEqual(after.body.bootId, before.body.bootId);
  assert.equal(after.body.lastSeq, 5);
  assert.equal(after.body.committedCount, 5);
  assert.deepEqual(h.state().ctx.container.applyCalls.slice(-5), exact);
});

test("durable replay verifies committed outcomes and fails closed on disagreement", async () => {
  const h = harness();
  await send(h, create());
  await admin(h, "destroy");
  h.state().ctx.container.alterOutcome = true;
  const result = await snapshot(h);
  assert.deepEqual(result, { status: 503, body: { ok: false, code: "replay_mismatch" } });
  assert.equal((await send(h, change("later"))).body.code, "replay_mismatch");
  assert.equal(h.state().ctx.storage.db.prepare("SELECT COUNT(*) AS n FROM journal").get().n, 1);
});

test("SQL enforces immutable journals and receipts", async () => {
  const h = harness();
  await send(h, create());
  const db = h.state().ctx.storage.db;
  for (const table of ["journal", "receipts"]) {
    assert.throws(() => db.exec(`DELETE FROM ${table}`), /immutable/);
    assert.throws(() => db.exec(`UPDATE ${table} SET seq = 2`), /immutable/);
  }
});

test("commands remain serialized across native awaits, duplicate retries, and reads", async () => {
  const h = harness();
  await send(h, create());
  const results = await Promise.all(Array.from({ length: 20 }, (_, i) => send(h, change(`id-${Math.floor(i / 2)}`))));
  assert.ok(results.every(r => r.status === 200));
  assert.equal((await snapshot(h)).body.sum, 30);
  assert.equal((await h.call("/durable/status")).body.lastSeq, 11);
  assert.equal(h.state().ctx.container.maxActive, 1);
});

test("native reply loss after commit retries safely and commits the original outcome", async () => {
  const h = harness();
  await send(h, create());
  h.state().ctx.container.loseReply = true;
  assert.equal((await send(h, change("lost"))).status, 503);
  assert.equal((await send(h, change("lost"))).body.value, 12);
  assert.equal((await snapshot(h)).body.sum, 12);
});

test("ephemeral state is lost, no old envelopes replay, fresh sequence starts at native status", async () => {
  const h = harness();
  await send(h, create(), "ephemeral");
  await send(h, change("inc"), "ephemeral");
  const before = (await h.call("/ephemeral/status")).body;
  h.restart("ephemeral");
  assert.equal((await send(h, change("inc"), "ephemeral")).body.value, 12);
  await admin(h, "destroy", {}, "ephemeral");
  const after = (await h.call("/ephemeral/status")).body;
  assert.equal(after.lastSeq, 0);
  assert.equal(after.journalCount, 0);
  assert.notEqual(after.bootId, before.bootId);
  assert.equal((await snapshot(h, "ephemeral")).body.count, 0);
  assert.equal(h.state("ephemeral").ctx.container.applyCalls.length, 2);
  assert.equal((await send(h, create(), "ephemeral")).body.seq, 1);
  assert.equal((await send(h, change("inc"), "ephemeral")).body.value, 12);
  assert.equal((await admin(h, "inject", { point: "after-native" }, "ephemeral")).status, 400);
});

test("ephemeral warm boot resolves unknown outcomes across DO eviction without duplicate mutation", async () => {
  const h = harness();
  await send(h, create(), "ephemeral");
  h.state("ephemeral").ctx.container.loseReply = true;
  assert.equal((await send(h, change("unknown"), "ephemeral")).status, 503);
  h.restart("ephemeral");
  assert.equal((await send(h, change("unknown"), "ephemeral")).body.value, 12);
  assert.equal((await send(h, change("fresh"), "ephemeral")).body.seq, 3);
  assert.equal((await snapshot(h, "ephemeral")).body.sum, 14);
});

test("boot marker lives on filesystem; bootstrap uses request origin/env and preserves warm native", async () => {
  const h = harness();
  await h.call("/durable/status");
  const c = h.state().ctx.container;
  const bootstrap = c.execs.find(exec => exec.command === BOOTSTRAP);
  assert.equal(bootstrap.options.env.CF_EXP_ARTIFACT_URL, "https://experiment.example/admin/artifact");
  assert.equal(bootstrap.options.env.LEANDB_TOKEN, "test-internal");
  assert.equal(bootstrap.command.includes("test-internal"), false);
  assert.match(bootstrap.command, /--db \/work\/state.sqlite serve --http 7411 --bind 0.0.0.0/);
  h.restart();
  await h.call("/durable/status");
  assert.equal(c.execs.filter(exec => exec.command === BOOTSTRAP).length, 1);
  assert.equal(c.starts.length, 1);
  assert.ok(c.timeouts.every(ms => ms === 5 * 60_000));
});

test("bootstrap errors are redacted and invalid requests never reach native", async () => {
  const h = harness();
  h.env.HOSTS.get("cf-v1:durable");
  h.state().ctx.container.bootFailure = true;
  const result = await h.call("/durable/status");
  assert.deepEqual(result, { status: 503, body: { ok: false, code: "container_exec_failed" } });
  assert.equal(JSON.stringify(result).includes("private bootstrap diagnostic"), false);
  assert.equal((await send(h, { requestId: "" })).status, 400);
  assert.equal((await send(h, { ...create(), command: { value: Number.MAX_SAFE_INTEGER + 1 } })).status, 400);
  assert.equal((await send(h, { ...create(), command: { key: "a".repeat(17000) } })).status, 413);
});

test("build exec streams NDJSON and holds the DO queue until the stream finishes", async () => {
  const h = harness();
  h.env.HOSTS.get("cf-v1:durable");
  let finish;
  h.state().ctx.container.execResponse = new Response(new ReadableStream({ start(controller) {
    controller.enqueue(new TextEncoder().encode(frame({ output: "building" })));
    finish = () => { controller.enqueue(new TextEncoder().encode(frame({ result: { ok: true, value: { exitCode: 0 } } }))); controller.close(); };
  } }), { headers: { "content-type": "application/x-ndjson" } });
  const response = await h.fetch("/durable/admin/exec", { command: "lake build", options: { cwd: "/work/repo", timeout: 60 } }, "test-admin");
  assert.equal(response.headers.get("content-type"), "application/x-ndjson");
  const consuming = response.text();
  let passed = false;
  const queued = h.call("/durable/admin/journal", undefined, "test-admin").then(r => { passed = true; return r; });
  await delay(10);
  assert.equal(passed, false);
  finish();
  assert.match(await consuming, /building/);
  assert.equal((await queued).status, 200);
  assert.equal(h.state().ctx.container.timeouts.at(-1), 30 * 60_000);
});

test("call whitelist, workspace streaming, stripped binary publish, protected download", async () => {
  const h = harness();
  assert.equal((await admin(h, "call", { method: "exec", args: [] })).status, 400);
  assert.equal((await admin(h, "exec", { command: "true", options: { timeout: 1600 } })).status, 400);
  assert.equal((await admin(h, "call", { method: "readTextFile", args: ["/work/repo/README.md"] })).body.value, "test-file");
  const upload = await worker.fetch(new Request("https://experiment.example/durable/admin/workspace", { method: "POST", headers: { authorization: "Bearer test-admin" }, body: new Uint8Array([31, 139]) }), h.env);
  assert.equal((await upload.json()).ok, true);
  assert.equal(h.state().ctx.container.workspace.url, "http://container/workspace?dir=/work/repo");
  const published = await admin(h, "publish");
  assert.equal(published.body.size, 8);
  assert.match(h.state().ctx.container.execs.at(-1).command, /strip \/work\/out\/cf-native.stripped/);
  assert.deepEqual(h.writes, ["cf-native"]);
  for (const token of ["test-admin", "test-internal"]) {
    const response = await h.fetch("/admin/artifact", undefined, token);
    assert.equal(response.status, 200);
    assert.equal(response.headers.get("content-length"), "8");
    assert.deepEqual(new Uint8Array(await response.arrayBuffer()), h.state().ctx.container.artifact);
  }
  assert.equal((await h.call("/admin/artifact", undefined, "test-bob")).status, 401);
});

test("only two fixed mode names are routed and container state is isolated", async () => {
  const h = harness();
  await send(h, create());
  assert.equal((await snapshot(h, "ephemeral")).body.count, 0);
  assert.deepEqual([...h.hosts.keys()].sort(), ["cf-v1:durable", "cf-v1:ephemeral"]);
  assert.equal((await h.call("/other/status")).status, 404);
});

test("canonicalization handles nested ordering, prototype keys, and numeric forms", () => {
  assert.equal(canonical({ b: { z: 1, a: 2 }, a: [1, -0] }), '{"a":[1,0],"b":{"a":2,"z":1}}');
  assert.equal(canonical(JSON.parse('{"__proto__":{"p":1},"constructor":2}')), '{"__proto__":{"p":1},"constructor":2}');
  assert.throws(() => canonical(Number.MAX_SAFE_INTEGER + 1), /unsafe_integer/);
});

test("native sequence regression triggers durable replay even with the same filesystem boot", async () => {
  const h = harness();
  await send(h, create());
  await send(h, change("inc"));
  const c = h.state().ctx.container, bootId = c.bootId;
  c.applied.clear(); c.counters.clear();
  assert.equal((await snapshot(h)).body.sum, 12);
  assert.equal(c.bootId, bootId);
  assert.equal(c.applyCalls.length, 4);
});

test("native state ahead of the durable journal is rejected without exposing a snapshot", async () => {
  const h = harness();
  await send(h, create());
  h.state().ctx.container.applied.set(2, {});
  assert.deepEqual(await snapshot(h), { status: 503, body: { ok: false, code: "native_ahead_of_journal" } });
});

test("unready Node server exits at the bounded readiness deadline", async () => {
  const h = harness();
  h.env.HOSTS.get("cf-v1:durable");
  const c = h.state().ctx.container;
  const originalNow = Date.now;
  let now = originalNow(), attempts = 0;
  Date.now = () => now;
  c.node = async () => { attempts++; now += 61_000; throw new Error("not listening"); };
  try {
    assert.deepEqual(await h.call("/durable/status"), { status: 503, body: { ok: false, code: "container_ready_timeout" } });
    assert.equal(attempts, 1);
  } finally { Date.now = originalNow; }
});

test("native readiness is bounded after launch and the gateway never exposes bootstrap diagnostics", async () => {
  const h = harness();
  h.env.HOSTS.get("cf-v1:durable");
  const c = h.state().ctx.container;
  const originalNow = Date.now;
  let now = originalNow(), attempts = 0;
  Date.now = () => now;
  c.native = async () => { attempts++; now += 61_000; throw new Error("private process failure"); };
  try {
    assert.deepEqual(await h.call("/durable/status"), { status: 503, body: { ok: false, code: "native_ready_timeout" } });
    assert.equal(attempts, 2);
  } finally { Date.now = originalNow; }
});

test("schema mismatch preserves an existing native process and refuses bootstrap", async () => {
  const h = harness();
  h.env.HOSTS.get("cf-v1:durable");
  const c = h.state().ctx.container;
  c.native = async () => ok({ ok: true, lastSeq: 0, schemaVersion: "other" });
  assert.equal((await h.call("/durable/status")).body.code, "native_schema_mismatch");
  assert.equal(c.execs.filter(exec => exec.command === BOOTSTRAP).length, 0);
});

test("publish rejection cancels the binary stream and releases the request queue", async () => {
  const h = harness();
  h.env.ARTIFACTS.put = async () => { throw new Error("storage rejected"); };
  assert.deepEqual(await admin(h, "publish"), { status: 503, body: { ok: false, code: "artifact_publish_failed" } });
  assert.equal((await h.call("/durable/admin/journal", undefined, "test-admin")).status, 200);
});

test("internal exec parses split NDJSON/UTF-8 and requires a successful terminal result", async () => {
  const native = new NativeContainer({}, {});
  const text = frame({ output: "compiling λ" }) + frame({ result: { ok: true, value: { exitCode: 0 } } });
  const bytes = new TextEncoder().encode(text);
  const port = { fetch: async () => new Response(new ReadableStream({ start(controller) {
    for (const byte of bytes) controller.enqueue(new Uint8Array([byte]));
    controller.close();
  } })) };
  await native.exec(port, "true", 1);
  await assert.rejects(native.exec({ fetch: async () => new Response(frame({ output: "no result" })) }, "true", 1), /container_exec_failed/);
  await assert.rejects(native.exec({ fetch: async () => new Response(frame({ result: { ok: true, value: { exitCode: 1 } } })) }, "false", 1), /container_exec_failed/);
});

test("static bootstrap is valid bash without executing it or interpolating credentials", () => {
  const parsed = spawnSync("bash", ["-n"], { input: BOOTSTRAP, encoding: "utf8" });
  assert.equal(parsed.status, 0, parsed.stderr);
  assert.equal(BOOTSTRAP.includes("test-internal"), false);
  assert.equal(BOOTSTRAP.includes("--auth-token"), false);
});
