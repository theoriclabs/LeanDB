import { DurableObject } from "cloudflare:workers";
import { BUILD_MS, CALLS, NativeContainer } from "./container.ts";
import { actor, admin, canonical, checkSchema, commandInput, envelope, failure, Fault, json, object, outcome, readJson, route, SCHEMA, type Actor, type Env, type Mode, type NativeStatus, type Outcome } from "./protocol.ts";

type JournalRow = { seq: number; actor: string; request_id: string; command: string; envelope: string; outcome: string | null };
type EphemeralRow = JournalRow & { boot_id: string };
type Reply = { response: Response; complete?: Promise<void> };
const SELECT_JOURNAL = "SELECT j.*, r.outcome FROM journal j LEFT JOIN receipts r ON r.seq = j.seq";

export class LeanDbHost extends DurableObject<Env> {
  private gate: Promise<void> = Promise.resolve();
  private readonly native: NativeContainer;
  private verifiedBoot: string | undefined;
  private verifiedSeq = 0;

  constructor(ctx: DurableObjectState, env: Env) {
    super(ctx, env);
    this.native = new NativeContainer(ctx, env);
    ctx.storage.sql.exec(`
      CREATE TABLE IF NOT EXISTS journal (
        seq INTEGER PRIMARY KEY CHECK(seq > 0), actor TEXT NOT NULL,
        request_id TEXT NOT NULL, command TEXT NOT NULL, envelope TEXT NOT NULL,
        UNIQUE(actor, request_id));
      CREATE TABLE IF NOT EXISTS receipts (
        seq INTEGER PRIMARY KEY REFERENCES journal(seq), outcome TEXT NOT NULL);
      CREATE TABLE IF NOT EXISTS control (key TEXT PRIMARY KEY, value TEXT NOT NULL);
      CREATE TABLE IF NOT EXISTS ephemeral_requests (
        boot_id TEXT NOT NULL, seq INTEGER NOT NULL, actor TEXT NOT NULL,
        request_id TEXT NOT NULL, command TEXT NOT NULL, envelope TEXT NOT NULL,
        outcome TEXT, PRIMARY KEY(boot_id, actor, request_id), UNIQUE(boot_id, seq));
      CREATE TRIGGER IF NOT EXISTS journal_no_update BEFORE UPDATE ON journal BEGIN SELECT RAISE(ABORT, 'immutable journal'); END;
      CREATE TRIGGER IF NOT EXISTS journal_no_delete BEFORE DELETE ON journal BEGIN SELECT RAISE(ABORT, 'immutable journal'); END;
      CREATE TRIGGER IF NOT EXISTS receipts_no_update BEFORE UPDATE ON receipts BEGIN SELECT RAISE(ABORT, 'immutable receipt'); END;
      CREATE TRIGGER IF NOT EXISTS receipts_no_delete BEFORE DELETE ON receipts BEGIN SELECT RAISE(ABORT, 'immutable receipt'); END;
    `);
  }

  override async fetch(request: Request): Promise<Response> {
    // DO input gates alone do not serialize external awaits. Keep the queue held
    // through native I/O, receipt durability, and the entire admin exec stream.
    const result: Promise<Reply> = this.gate.then(() => this.handle(request)).catch(error => ({ response: failure(error) }));
    this.gate = result.then(async reply => { await reply.complete; }).catch(() => {});
    this.ctx.waitUntil(this.gate);
    return (await result).response;
  }

  private async handle(request: Request): Promise<Reply> {
    const target = route(request);
    if (!target) throw new Fault("not_found", 404);
    const { mode, action } = target;
    const who = action.startsWith("admin/") ? (admin(request, this.env), undefined) : actor(request, this.env);
    checkSchema(request);
    const expectedMethod = action === "status" || action === "admin/journal" ? "GET" : "POST";
    if (request.method !== expectedMethod) throw new Fault("method_not_allowed", 405);
    this.bindMode(mode);
    if (action.startsWith("admin/")) return this.administration(request, mode, action);
    const body = action === "status" ? undefined : await readJson(request);
    // Validate transport before starting a container or recovering old commands.
    const input = action === "command" ? commandInput(body!) : undefined;
    if (action === "snapshot" && typeof body!.tenant !== "string") throw new Fault("invalid_snapshot", 400);
    const ready = await this.native.ensure(new URL(request.url).origin);
    let status = ready.status;
    if (mode === "durable") {
      await this.recover(ready.bootId, status);
      status = { ...status, lastSeq: this.journalCount() };
    } else {
      status = await this.prepareEphemeral(ready.bootId, status);
    }
    if (action === "status") return { response: json({ ...status, mode, bootId: ready.bootId, journalCount: this.journalCount(), committedCount: this.receiptCount() }) };
    if (action === "snapshot") return { response: json(await this.native.query("snapshot", [JSON.stringify({ actor: who, tenant: body!.tenant })])) };
    const result = mode === "durable"
      ? await this.durableCommand(who!, input!.requestId, input!.command)
      : await this.ephemeralCommand(ready.bootId, status, who!, input!.requestId, input!.command);
    return { response: json(result) };
  }

  private bindMode(mode: Mode): void {
    this.ctx.storage.sql.exec("INSERT OR IGNORE INTO control (key, value) VALUES ('mode', ?)", mode);
    if (this.control("mode") !== mode) throw new Fault("mode_mismatch", 409);
  }
  private control(key: string): string | undefined {
    return this.ctx.storage.sql.exec<{ value: string }>("SELECT value FROM control WHERE key = ?", key).toArray()[0]?.value;
  }
  private journalCount(): number { return this.ctx.storage.sql.exec<{ n: number }>("SELECT COUNT(*) AS n FROM journal").one().n; }
  private receiptCount(): number { return this.ctx.storage.sql.exec<{ n: number }>("SELECT COUNT(*) AS n FROM receipts").one().n; }

  private async apply(row: Pick<JournalRow, "seq" | "envelope">): Promise<Outcome> {
    return outcome(await this.native.query("apply", [row.envelope]), row.seq);
  }

  private async recover(bootId: string, status: NativeStatus): Promise<void> {
    const count = this.journalCount();
    if (status.lastSeq > count) throw new Fault("native_ahead_of_journal");
    if (this.verifiedBoot !== bootId || status.lastSeq < this.verifiedSeq) {
      this.verifiedSeq = 0;
      this.verifiedBoot = bootId;
    }
    const deadline = Date.now() + 120_000;
    for (;;) {
      const rows = this.ctx.storage.sql.exec<JournalRow>(`${SELECT_JOURNAL} WHERE j.seq > ? ORDER BY j.seq LIMIT 100`, this.verifiedSeq).toArray();
      if (!rows.length) return;
      for (const row of rows) {
        if (Date.now() >= deadline) throw new Fault("replay_timeout");
        if (row.seq !== this.verifiedSeq + 1) throw new Fault("journal_gap");
        const result = canonical(await this.apply(row));
        if (row.outcome !== null && result !== row.outcome) throw new Fault("replay_mismatch");
        if (row.outcome === null) {
          this.ctx.storage.sql.exec("INSERT INTO receipts (seq, outcome) VALUES (?, ?)", row.seq, result);
          await this.ctx.storage.sync();
        }
        // Advance only after verifying the full committed outcome or syncing the
        // previously interrupted operation's receipt. Failures remain retryable.
        this.verifiedSeq = row.seq;
      }
    }
  }

  private async durableCommand(who: Actor, requestId: string, command: string): Promise<Outcome> {
    const prior = this.ctx.storage.sql.exec<JournalRow>(`${SELECT_JOURNAL} WHERE j.actor = ? AND j.request_id = ?`, who, requestId).toArray()[0];
    if (prior) {
      if (prior.command !== command) throw new Fault("request_id_conflict", 409);
      if (prior.outcome === null) throw new Fault("receipt_missing");
      return JSON.parse(prior.outcome) as Outcome;
    }
    const seq = this.journalCount() + 1;
    if (!Number.isSafeInteger(seq)) throw new Fault("sequence_exhausted");
    const exact = envelope(seq, who, requestId, command);
    const point = this.control("inject");
    this.ctx.storage.transactionSync(() => {
      this.ctx.storage.sql.exec("INSERT INTO journal (seq, actor, request_id, command, envelope) VALUES (?, ?, ?, ?, ?)", seq, who, requestId, command, exact);
      this.ctx.storage.sql.exec("DELETE FROM control WHERE key = 'inject'");
    });
    // Explicit write-ahead durability, including consuming the one-shot fault.
    await this.ctx.storage.sync();
    if (point === "after-journal") throw new Fault("injected_after_journal");
    const result = await this.apply({ seq, envelope: exact });
    if (point === "after-native") throw new Fault("injected_after_native");
    this.ctx.storage.sql.exec("INSERT INTO receipts (seq, outcome) VALUES (?, ?)", seq, canonical(result));
    await this.ctx.storage.sync();
    this.verifiedSeq = seq;
    return result;
  }

  private async prepareEphemeral(bootId: string, status: NativeStatus): Promise<NativeStatus> {
    // Receipts/pending transport attempts are scoped to this filesystem boot.
    // Never replay an envelope from a destroyed container, even on an ID retry.
    this.ctx.storage.sql.exec("DELETE FROM ephemeral_requests WHERE boot_id <> ?", bootId);
    const latest = this.ctx.storage.sql.exec<{ n: number }>("SELECT COALESCE(MAX(seq), 0) AS n FROM ephemeral_requests WHERE boot_id = ? AND outcome IS NOT NULL", bootId).one().n;
    if (status.lastSeq < latest) {
      this.ctx.storage.sql.exec("DELETE FROM ephemeral_requests WHERE boot_id = ?", bootId);
    }
    const pending = this.ctx.storage.sql.exec<EphemeralRow>("SELECT * FROM ephemeral_requests WHERE boot_id = ? AND outcome IS NULL ORDER BY seq", bootId).toArray();
    for (const row of pending) {
      const result = await this.apply(row);
      this.ctx.storage.sql.exec("UPDATE ephemeral_requests SET outcome = ? WHERE boot_id = ? AND seq = ?", canonical(result), bootId, row.seq);
    }
    if (pending.length) {
      await this.ctx.storage.sync();
      return { ...status, lastSeq: Math.max(status.lastSeq, pending[pending.length - 1]!.seq) };
    }
    return status;
  }

  private async ephemeralCommand(bootId: string, status: NativeStatus, who: Actor, requestId: string, command: string): Promise<Outcome> {
    const prior = this.ctx.storage.sql.exec<EphemeralRow>("SELECT * FROM ephemeral_requests WHERE boot_id = ? AND actor = ? AND request_id = ?", bootId, who, requestId).toArray()[0];
    if (prior) {
      if (prior.command !== command) throw new Fault("request_id_conflict", 409);
      if (prior.outcome === null) throw new Fault("receipt_missing");
      return JSON.parse(prior.outcome) as Outcome;
    }
    const seq = status.lastSeq + 1;
    if (!Number.isSafeInteger(seq)) throw new Fault("sequence_exhausted");
    const exact = envelope(seq, who, requestId, command);
    this.ctx.storage.sql.exec("INSERT INTO ephemeral_requests (boot_id, seq, actor, request_id, command, envelope) VALUES (?, ?, ?, ?, ?, ?)", bootId, seq, who, requestId, command, exact);
    await this.ctx.storage.sync();
    const result = await this.apply({ seq, envelope: exact });
    this.ctx.storage.sql.exec("UPDATE ephemeral_requests SET outcome = ? WHERE boot_id = ? AND seq = ?", canonical(result), bootId, seq);
    await this.ctx.storage.sync();
    return result;
  }

  private async administration(request: Request, mode: Mode, action: string): Promise<Reply> {
    if (action === "admin/journal") return { response: json({ count: this.journalCount() }) };
    if (action === "admin/destroy") {
      await this.native.destroy();
      this.verifiedBoot = undefined;
      this.verifiedSeq = 0;
      return { response: json({ ok: true }) };
    }
    if (mode !== "durable") throw new Fault("durable_only", 400);
    if (action === "admin/inject") {
      const { point } = await readJson(request);
      if (point !== "after-journal" && point !== "after-native") throw new Fault("invalid_injection", 400);
      this.ctx.storage.sql.exec("INSERT INTO control (key, value) VALUES ('inject', ?) ON CONFLICT(key) DO UPDATE SET value = excluded.value", point);
      await this.ctx.storage.sync();
      return { response: json({ ok: true, point }) };
    }
    // The administrative build surface is trusted and intentionally powerful.
    // It is not available through actor tokens or the ephemeral container.
    if (action === "admin/workspace") {
      if (!request.body) throw new Fault("workspace_body_required", 400);
      const port = await this.native.node(true);
      return this.stream(await port.fetch("http://container/workspace?dir=/work/repo", {
        method: "POST", body: request.body, signal: AbortSignal.timeout(BUILD_MS),
      }));
    }
    if (action === "admin/exec" || action === "admin/call") {
      const body = await readJson(request, 1024 * 1024);
      if (action === "admin/call") {
        if (typeof body.method !== "string" || !CALLS.has(body.method) || !Array.isArray(body.args)) throw new Fault("invalid_call", 400);
      } else {
        if (!(typeof body.command === "string" && body.command.length > 0) &&
          !(Array.isArray(body.command) && body.command.length > 0 && body.command.every(arg => typeof arg === "string"))) throw new Fault("invalid_exec", 400);
        if (body.options !== undefined && !object(body.options)) throw new Fault("invalid_exec", 400);
        const options = (body.options ?? {}) as Record<string, unknown>;
        const timeout = options.timeout ?? 25 * 60;
        if (typeof timeout !== "number" || !Number.isFinite(timeout) || timeout <= 0 || timeout > 25 * 60) throw new Fault("invalid_timeout", 400);
        body.options = { ...options, timeout };
      }
      // A build command can change the binary/database; force verification on
      // the next runtime request even if the container's boot marker survives.
      this.verifiedBoot = undefined;
      const port = await this.native.node(true);
      return this.stream(await port.fetch(`http://container/env/${action.slice(6)}`, {
        method: "POST", headers: { "content-type": "application/json" }, body: JSON.stringify(body),
        signal: AbortSignal.timeout(BUILD_MS),
      }));
    }
    const port = await this.native.node(true);
    await this.native.exec(port, "set -eu\ncp /work/out/cf-native /work/out/cf-native.stripped\nstrip /work/out/cf-native.stripped\nchmod 700 /work/out/cf-native.stripped\nmv /work/out/cf-native.stripped /work/out/cf-native", 60);
    const info = await this.native.call(port, "fileInfo", ["/work/out/cf-native"]);
    if (info.ok !== true || !object(info.value) || !Number.isSafeInteger(info.value.size) || (info.value.size as number) <= 0) throw new Fault("artifact_read_failed");
    const size = info.value.size as number;
    const raw = await port.fetch("http://container/out/raw?path=cf-native", { signal: AbortSignal.timeout(120_000) });
    if (!raw.ok || !raw.body) throw new Fault("artifact_read_failed");
    // Node's /out/raw is chunked. R2 requires a known-length stream; this
    // enforces fileInfo's byte count without buffering the binary in the Worker.
    const { readable, writable } = new FixedLengthStream(size);
    const abort = new AbortController();
    const piping = raw.body.pipeTo(writable, { signal: abort.signal });
    const saving = this.env.ARTIFACTS.put("cf-native", readable, { httpMetadata: { contentType: "application/octet-stream" } });
    let saved: R2Object | null;
    try {
      [saved] = await Promise.all([saving, piping]);
    } catch {
      abort.abort();
      // If R2 rejected before taking a reader, an outstanding backpressured
      // write cannot finish aborting until the readable side is cancelled.
      await readable.cancel().catch(() => {});
      await piping.catch(() => {});
      throw new Fault("artifact_publish_failed");
    }
    if (!saved) throw new Fault("artifact_publish_failed");
    return { response: json({ ok: true, key: "cf-native", size: saved.size, etag: saved.httpEtag }) };
  }

  private stream(response: Response): Reply {
    const headers = new Headers({ "content-type": response.headers.get("content-type") ?? "application/octet-stream", "cache-control": "no-store", "x-experiment-schema": SCHEMA });
    if (!response.body) return { response: new Response(null, { status: response.status, headers }) };
    const { readable, writable } = new TransformStream<Uint8Array, Uint8Array>();
    const complete = response.body.pipeTo(writable);
    // Attach rejection handling immediately; the queue itself also awaits it.
    this.ctx.waitUntil(complete.catch(() => {}));
    return { response: new Response(readable, { status: response.status, headers }), complete };
  }
}
