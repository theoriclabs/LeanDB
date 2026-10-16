import { Fault, object, SCHEMA, unwrap, type Env, type NativeStatus } from "./protocol.ts";

export const BUILD_MS = 30 * 60_000;
const RUNTIME_MS = 5 * 60_000;
const READY_MS = 60_000;
export const CALLS = new Set([
  "absolutePath", "joinPath", "readTextFile", "readTextLines", "readBinaryFile", "writeFile", "appendFile",
  "truncateFile", "flushFile", "renameFile", "fileInfo", "listDir", "canonicalPath", "exists", "createDir", "remove",
  "createTempDir", "createTempFile", "cleanup",
]);

// Static command: secret values only travel in options.env, never in the command.
export const BOOTSTRAP = `set -eu
umask 077
mkdir -p /work/out
if [ -s /work/native.pid ] && kill -0 "$(cat /work/native.pid)" 2>/dev/null; then exit 0; fi
curl --fail --silent --show-error --connect-timeout 5 --max-time 30 \
  --header "Authorization: Bearer $CF_EXP_INTERNAL_TOKEN" \
  "$CF_EXP_ARTIFACT_URL" --output /work/out/cf-native.download
chmod 700 /work/out/cf-native.download
mv /work/out/cf-native.download /work/out/cf-native
nohup /work/out/cf-native --db /work/state.sqlite serve --http 7411 --bind 0.0.0.0 \
  </dev/null >/work/native.log 2>&1 &
echo $! >/work/native.pid`;

export class NativeContainer {
  constructor(private readonly ctx: DurableObjectState, private readonly env: Env) {}

  private get container(): Container {
    if (!this.ctx.container) throw new Fault("container_unconfigured");
    return this.ctx.container;
  }

  async node(build = false): Promise<Fetcher> {
    const container = this.container;
    if (!container.running) container.start({ enableInternet: true });
    await container.setInactivityTimeout(build ? BUILD_MS : RUNTIME_MS);
    const port = container.getTcpPort(8080);
    const deadline = Date.now() + READY_MS;
    while (Date.now() < deadline) {
      let response: Response | undefined;
      try { response = await port.fetch("http://container/health", { signal: AbortSignal.timeout(3000) }); } catch { /* booting */ }
      if (response) {
        const body: unknown = await response.json().catch(() => null);
        if (response.ok && object(body) && body.ok === true && body.protocol === 4) return port;
        if (response.ok) throw new Fault("container_protocol_mismatch");
      }
      await new Promise(resolve => setTimeout(resolve, 250));
    }
    throw new Fault("container_ready_timeout");
  }

  async ensure(origin: string): Promise<{ bootId: string; status: NativeStatus }> {
    if (!this.env.INTERNAL_TOKEN) throw new Fault("internal_token_missing");
    const port = await this.node();
    const bootId = await this.bootId(port);
    const status = await this.probe();
    if (status) return { bootId, status };
    await this.exec(port, BOOTSTRAP, 40, {
      CF_EXP_INTERNAL_TOKEN: this.env.INTERNAL_TOKEN,
      CF_EXP_ARTIFACT_URL: new URL("/admin/artifact", origin).href,
      LEANDB_TOKEN: this.env.INTERNAL_TOKEN,
    });
    const deadline = Date.now() + READY_MS;
    while (Date.now() < deadline) {
      const ready = await this.probe();
      if (ready) return { bootId, status: ready };
      await new Promise(resolve => setTimeout(resolve, 250));
    }
    throw new Fault("native_ready_timeout");
  }

  async destroy(): Promise<void> { await this.container.destroy(); }

  async query(name: string, args: string[], timeout = 15_000): Promise<Record<string, unknown>> {
    const response = await this.nativeFetch(name, args, timeout);
    if (!response.ok) { await response.body?.cancel(); throw new Fault("native_unavailable"); }
    return unwrap(await response.json());
  }

  private nativeFetch(name: string, args: string[], timeout: number): Promise<Response> {
    return this.container.getTcpPort(7411).fetch(`http://native/query/${name}`, {
      method: "POST", headers: { authorization: `Bearer ${this.env.INTERNAL_TOKEN}`, "content-type": "application/json" },
      body: JSON.stringify({ args }), signal: AbortSignal.timeout(timeout),
    });
  }

  private async probe(): Promise<NativeStatus | undefined> {
    let response: Response;
    try { response = await this.nativeFetch("status", [], 2000); } catch { return undefined; }
    if (!response.ok) { await response.body?.cancel(); throw new Fault("native_status_unavailable"); }
    const status = unwrap(await response.json());
    if (status.ok !== true || !Number.isSafeInteger(status.lastSeq) || (status.lastSeq as number) < 0) throw new Fault("native_status_invalid");
    if (status.schemaVersion !== SCHEMA) throw new Fault("native_schema_mismatch");
    return status as NativeStatus;
  }

  private async bootId(port: Fetcher): Promise<string> {
    let result = await this.call(port, "readTextFile", ["/work/boot-id"]);
    if (result.ok !== true) {
      await this.exec(port, `set -eu\numask 077\nif [ ! -s /work/boot-id ]; then printf '%s' '${crypto.randomUUID()}' > /work/boot-id; fi`, 5);
      result = await this.call(port, "readTextFile", ["/work/boot-id"]);
    }
    if (result.ok !== true || typeof result.value !== "string" || !/^[0-9a-f-]{36}$/.test(result.value.trim())) throw new Fault("boot_id_invalid");
    return result.value.trim();
  }

  async call(port: Fetcher, method: string, args: unknown[]): Promise<Record<string, unknown>> {
    const response = await port.fetch("http://container/env/call", {
      method: "POST", headers: { "content-type": "application/json" },
      body: JSON.stringify({ method, args }), signal: AbortSignal.timeout(15_000),
    });
    if (!response.ok) { await response.body?.cancel(); throw new Fault("container_call_failed"); }
    const value: unknown = await response.json();
    if (!object(value)) throw new Fault("container_call_failed");
    return value;
  }

  async exec(port: Fetcher, command: string, timeout: number, env: Record<string, string> = {}): Promise<void> {
    const response = await port.fetch("http://container/env/exec", {
      method: "POST", headers: { "content-type": "application/json" },
      body: JSON.stringify({ command, options: { cwd: "/work", timeout, env } }),
      signal: AbortSignal.timeout((timeout + 5) * 1000),
    });
    if (!response.ok || !response.body) { await response.body?.cancel(); throw new Fault("container_exec_failed"); }
    // Consume NDJSON incrementally and discard output. Neither output nor errors
    // from internal bootstrap are logged or reflected to callers.
    const reader = response.body.getReader();
    const decoder = new TextDecoder();
    let pending = "";
    let result: unknown;
    const frame = (line: string) => {
      if (!line.trim()) return;
      const parsed: unknown = JSON.parse(line);
      if (object(parsed) && Object.hasOwn(parsed, "result")) result = parsed.result;
    };
    try {
      for (;;) {
        const { value, done } = await reader.read();
        pending += done ? decoder.decode() : decoder.decode(value, { stream: true });
        let newline: number;
        while ((newline = pending.indexOf("\n")) >= 0) { frame(pending.slice(0, newline)); pending = pending.slice(newline + 1); }
        if (pending.length > 1024 * 1024) throw new Fault("container_exec_protocol");
        if (done) { frame(pending); break; }
      }
    } catch { await reader.cancel().catch(() => {}); throw new Fault("container_exec_failed"); }
    finally { reader.releaseLock(); }
    if (!object(result) || result.ok !== true || !object(result.value) || result.value.exitCode !== 0) throw new Fault("container_exec_failed");
  }
}
