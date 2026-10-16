import { actor, admin, checkSchema, failure, Fault, hasToken, json, route, SCHEMA, type Env } from "./protocol.ts";
export { LeanDbHost } from "./host.ts";

export default {
  async fetch(request: Request, env: Env): Promise<Response> {
    try {
      const path = new URL(request.url).pathname;
      if (path === "/health" && request.method === "GET") {
        checkSchema(request);
        return json({ ok: true, schemaVersion: SCHEMA, modes: ["durable", "ephemeral"] });
      }
      if (path === "/admin/artifact") {
        if (!hasToken(request, env.ADMIN_TOKEN) && !hasToken(request, env.INTERNAL_TOKEN)) throw new Fault("unauthorized", 401);
        checkSchema(request);
        if (request.method !== "GET") throw new Fault("method_not_allowed", 405);
        const artifact = await env.ARTIFACTS.get("cf-native");
        if (!artifact) throw new Fault("artifact_missing", 404);
        return new Response(artifact.body, { headers: {
          "content-type": "application/octet-stream", "content-length": String(artifact.size),
          etag: artifact.httpEtag, "cache-control": "no-store", "x-experiment-schema": SCHEMA,
        } });
      }
      const target = route(request);
      if (!target) throw new Fault("not_found", 404);
      if (target.action.startsWith("admin/")) admin(request, env); else actor(request, env);
      checkSchema(request);
      // Exactly two names. No user-controlled DO IDs or per-tenant containers.
      return await env.HOSTS.get(env.HOSTS.idFromName(`${SCHEMA}:${target.mode}`)).fetch(request);
    } catch (error) { return failure(error); }
  },
} satisfies ExportedHandler<Env>;
