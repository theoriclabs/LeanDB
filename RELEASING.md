# Releasing LeanDB

LeanDB uses the version in `lakefile.toml` as its package version. The Lean toolchain and the pinned `leansqlite` revision must move together; every example package must use the same `lean-toolchain` file as the repository root.

Before tagging a release:

1. Add the release date and final notes to `CHANGELOG.md`.
2. Run `./scripts/release_check.sh` from the repository root.
3. Review `git diff --check` and `git status --short`. The release commit should contain only intended source, documentation, and lockfile changes.
4. Confirm that the repository's MIT `LICENSE` file is present and carries the intended copyright holder and year.
5. Commit the release, then create an annotated tag matching the Lake version, for example `v0.8.1`.
6. Push the commit and tag. Publish a GitHub release using the changelog entry.

The release check builds the engine, importer, and precompiled consumers
of the client and native interpreter, runs the engine and DDD suites,
checks the portable model's import closure and negative
fixtures, runs the model suite in memory and on SQLite,
builds and runs the remaining example suites (including `legacy`'s frozen V0→V1
migration drill), builds and runs `examples/dashboard` (importing two
bases and querying in-process, over stdio, and over the bundled
opt-in HTTP package), scaffolds a base with
`leandb new` against the checkout and runs its tests (twice, to check
the overwrite refusal), smokes `serve --http` (typed routes, `/rpc`,
the bearer-token gate, a stale `X-LeanDb-Fingerprint`), `serve --mcp`
(`tools/list`, `tools/call`), and `leandb host` (two bases under one
port), and exercises fresh SQLite import generation plus overwrite
refusal.

Bases pulled out of this repository require the engine by git tag
(`leandb new … --leandb-git <url> --rev v0.8.1`); a tag therefore fixes
the engine's `Base`/`Cli`/`Client` surface and the wire (JSON-lines argv,
row JSON, error codes, `X-LeanDb-Fingerprint`). Bump the version in
`lakefile.toml` and `LeanDb/Mcp.lean`'s `serverInfo` together. Update the
version examples in this guide and the status in `docs/roadmap.md` too.

The opt-in package in `packages/leandb-http` ships under the LeanDB tag.
Bump its Lake version and the install example in its README with the
root version. Its lockfile pins LeanHttp, and its toolchain matches the
root. The dashboard verifies the adapter from the same checkout.
Verify that a downstream consumer can require the adapter from the tag
with Lake's Git subdirectory field.

Use `git diff --check` and check local Markdown links before publishing.
Current documentation lives in `docs/`; historical proposal references in
old changelog entries describe earlier releases.
