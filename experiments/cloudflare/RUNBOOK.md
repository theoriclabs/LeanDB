# Reproducing the experiment

Start with [PLAN.md](PLAN.md) and [PROTOCOL.md](PROTOCOL.md). Final results belong in README.md and evidence/. Commands below create real cloud resources and are intended for an authorized operator.

## Prerequisites

- Cloudflare account with Workers, SQLite Durable Objects, Containers and R2.
- Wrangler 4.148.0 was used. The original run used the installation at /Users/harshwork/code/wybe/runtime/node_modules/.bin/wrangler.
- Node 24, Python 3.9+, and repository source at the pinned revisions.
- The configured immutable container image in the same account. It contains Debian, Node, a private execution server, curl, C build tools and elan. Its source is Wybe runtime/container/Dockerfile and runtime/container/server.mjs; the exact deployed image digest is in gateway/wrangler.jsonc and evidence/resources.json. Do not delete this shared image during cleanup.
- A private JSON file containing four independent random tokens: ADMIN_TOKEN, INTERNAL_TOKEN, TOKEN_A, TOKEN_B. Keep it outside the repository with permissions 0600. Never print token values.

The gateway was validated using the already installed dependency directory via a local ignored node_modules symlink. Follow gateway/README.md for checks. This experiment does not add runtime dependencies to LeanDB.

## Setup and build

1. Choose unique Worker/bucket names and update account_id and the image in gateway/wrangler.jsonc.
2. Create the R2 bucket using Wrangler. Deploy the gateway and set the four secrets with wrangler secret bulk using the private token file.
3. Package source with package-source.py. It exports LeanDB commit 8920c70 and LeanOntology commit 322a4c12631dd8ece6ae9841a5e6b630d08d1e3b, plus the experiment's current native fixture. It vendors the pinned LeanOntology source through a temporary local dependency override; no repository dependency declaration is modified. leansqlite remains pinned to 0be4df908d1a8e75b58961041e2b4973692623df.
4. Upload the source tar with admin.py workspace. admin.py defaults to the original run URL and private token path; change these for a new deployment. Build endpoints require ADMIN_TOKEN.
5. Start build-cloud.sh inside /work/repo using admin.py exec. For a long build, launch it with nohup and redirect output and exit status to /work/build.log and /work/build.exit. This avoids tying the build lifetime to an HTTP request. Bound the process with timeout.
6. Collect the full build log, exit code, executable SHA-256 and shared-library dependencies. Only proceed after exit0.
7. Run admin.py publish to stream the stripped executable into the private R2 key cf-native. The first runtime request downloads it into each disposable container.
8. Obtain authenticated status for both modes before probing. This separates cold bootstrap problems from domain assertion failures.

bootstrap.ts/bootstrap.jsonc were an initial administrative-only deployment while the terminal worker implemented the full gateway. They use the same durable object identity. They are not needed when reproducing from the finished gateway.

## Live probes

Run in this order, supplying the private credentials file and explicit --execute:

1. probes/run.py <URL> --mode full --tokens-file <file> --checkpoint <checkpoint> --evidence <new-output> --execute
2. Redeploy the same gateway with Wrangler; save its output/version.
3. probes/run.py <URL> --mode redeploy-check with the same checkpoint and a new evidence path.
4. extra-crash-probes.py --url <URL> --tokens <file> --evidence <new-output>

The extra probes add commands, so run them after redeploy-check; otherwise the saved checkpoint no longer represents the complete state. Do not run another client concurrently. Each full run expects fresh mode state or uses the probe runner's documented preconditions.

The main runner saves actual responses, assertions, failure category, timings and a checkpoint without tokens. A returned nonzero exit is a failed or incomplete experiment, never a pass. Its request budget is cumulative across full and redeploy-check. Extra probes use 18 requests without retries; keep the total under the plan's 1000-request bound.

## Cleanup

Collect evidence first. Destroy both experiment containers through the authenticated admin endpoints. Remove only the experiment container application, Worker/DO namespace and R2 cf-native object and bucket. Verify the experiment application is absent and the existing wybe-runtime application remains. Do not remove the shared image. Update evidence/resources.json with cleanup status and retain command receipts.
