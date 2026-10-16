export const SCHEMA = "cf-v1";
export type Mode = "durable" | "ephemeral";
export type Actor = "alice" | "bob";
export interface Env {
  HOSTS: DurableObjectNamespace;
  ARTIFACTS: R2Bucket;
  ADMIN_TOKEN: string;
  INTERNAL_TOKEN: string;
  TOKEN_A: string;
  TOKEN_B: string;
}
export type Json = null | boolean | number | string | Json[] | { [key: string]: Json };
export type Outcome = { ok: boolean; seq: number; code?: string; value?: number };
export type NativeStatus = { ok: true; lastSeq: number; schemaVersion: string };

export class Fault extends Error {
  constructor(readonly code: string, readonly status = 503) { super(code); }
}
export function object(value: unknown): value is Record<string, unknown> {
  return value !== null && typeof value === "object" && !Array.isArray(value);
}
// Serialize directly so even integer-looking property names have a defined order.
export function canonical(value: unknown, depth = 0): string {
  if (depth > 32) throw new Fault("invalid_json", 400);
  if (value === null || typeof value === "boolean" || typeof value === "string") return JSON.stringify(value);
  if (typeof value === "number" && Number.isFinite(value)) {
    if (Number.isInteger(value) && !Number.isSafeInteger(value)) throw new Fault("unsafe_integer", 400);
    return JSON.stringify(value);
  }
  if (Array.isArray(value)) return `[${value.map(v => canonical(v, depth + 1)).join(",")}]`;
  if (object(value)) return `{${Object.keys(value).sort().map(k => `${JSON.stringify(k)}:${canonical(value[k], depth + 1)}`).join(",")}}`;
  throw new Fault("invalid_json", 400);
}
export function json(value: unknown, status = 200): Response {
  return Response.json(value, { status, headers: {
    "cache-control": "no-store", "x-experiment-schema": SCHEMA,
    ...(status === 401 ? { "www-authenticate": "Bearer" } : {}),
    ...(status === 503 ? { "retry-after": "1" } : {}),
  } });
}
export function failure(error: unknown): Response {
  // Never reflect raw exceptions, commands, environment, or authorization headers.
  return error instanceof Fault ? json({ ok: false, code: error.code }, error.status)
    : json({ ok: false, code: "unavailable" }, 503);
}
export function checkSchema(request: Request): void {
  const schema = request.headers.get("x-experiment-schema");
  if (schema !== null && schema !== SCHEMA) throw new Fault("schema_mismatch", 409);
}
export function hasToken(request: Request, secret: string | undefined): boolean {
  if (!secret) return false;
  const match = /^Bearer ([^\s]+)$/i.exec(request.headers.get("authorization") ?? "");
  if (!match) return false;
  const actual = match[1]!;
  let diff = actual.length ^ secret.length;
  for (let i = 0; i < secret.length; i++) diff |= secret.charCodeAt(i) ^ (actual.charCodeAt(i) || 0);
  return diff === 0;
}
export function admin(request: Request, env: Env): void {
  if (!hasToken(request, env.ADMIN_TOKEN)) throw new Fault("unauthorized", 401);
}
export function actor(request: Request, env: Env): Actor {
  if (hasToken(request, env.TOKEN_A)) return "alice";
  if (hasToken(request, env.TOKEN_B)) return "bob";
  throw new Fault("unauthorized", 401);
}
export function route(request: Request): { mode: Mode; action: string } | undefined {
  const match = /^\/(durable|ephemeral)\/(command|snapshot|status|admin\/(?:inject|destroy|journal|workspace|exec|call|publish))$/.exec(new URL(request.url).pathname);
  return match ? { mode: match[1] as Mode, action: match[2]! } : undefined;
}
export async function readJson(request: Request, limit = 16 * 1024): Promise<Record<string, unknown>> {
  if (!request.body) throw new Fault("invalid_json", 400);
  const reader = request.body.getReader();
  const chunks: Uint8Array[] = [];
  let length = 0;
  try {
    for (;;) {
      const { value, done } = await reader.read();
      if (done) break;
      length += value.byteLength;
      if (length > limit) { await reader.cancel(); throw new Fault("body_too_large", 413); }
      chunks.push(value);
    }
  } finally { reader.releaseLock(); }
  const bytes = new Uint8Array(length);
  let offset = 0;
  for (const chunk of chunks) { bytes.set(chunk, offset); offset += chunk.byteLength; }
  try {
    const value: unknown = JSON.parse(new TextDecoder("utf-8", { fatal: true, ignoreBOM: false }).decode(bytes));
    if (!object(value)) throw new Error();
    return value;
  } catch { throw new Fault("invalid_json", 400); }
}
export function commandInput(body: Record<string, unknown>): { requestId: string; command: string } {
  if (typeof body.requestId !== "string" || body.requestId.length < 1 || body.requestId.length > 256 || !object(body.command)) {
    throw new Fault("invalid_command_request", 400);
  }
  return { requestId: body.requestId, command: canonical(body.command) };
}
export function envelope(seq: number, who: Actor, requestId: string, command: string): string {
  // This exact immutable string, never reconstructed, is passed on every retry.
  return `{"seq":${seq},"actor":${JSON.stringify(who)},"requestId":${JSON.stringify(requestId)},"command":${command}}`;
}
export function unwrap(value: unknown): Record<string, unknown> {
  if (!object(value)) throw new Fault("native_protocol");
  if (value.ok === true && Object.hasOwn(value, "result")) {
    if (!object(value.result)) throw new Fault("native_protocol");
    return value.result;
  }
  return value;
}
export function outcome(value: Record<string, unknown>, seq: number): Outcome {
  if (typeof value.ok !== "boolean" || value.seq !== seq ||
    (value.value !== undefined && !Number.isSafeInteger(value.value)) ||
    (value.ok === false && !["forbidden", "duplicate", "not_found", "rolled_back", "invalid"].includes(String(value.code)))) {
    throw new Fault("native_outcome_invalid");
  }
  return value as Outcome;
}
