#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
cd "$repo_root"

for base in tickets crm shop gpumarket eats legacy dashboard; do
  if ! cmp -s lean-toolchain "examples/$base/lean-toolchain"; then
    echo "release check failed: examples/$base/lean-toolchain differs from root" >&2
    exit 1
  fi
done

lake build leandb leandb_tests
.lake/build/bin/leandb_tests

for base in tickets crm shop gpumarket eats; do
  (
    cd "examples/$base"
    lake build "$base" "${base}_tests"
    ".lake/build/bin/${base}_tests"
    if [[ "$base" == "eats" ]]; then
      lake build eats_offers_tests
      .lake/build/bin/eats_offers_tests
    fi
    schema_json=$(".lake/build/bin/$base" schema)
    if [[ "$schema_json" != *'"ok":true'* ]]; then
      echo "release check failed: $base schema smoke test failed" >&2
      exit 1
    fi
  )
done

# dashboard: the same typed query in-process, over stdio, and over leanhttp.
# examples/dashboard requires the untracked sibling ../../../leandb-http
# (see RELEASING.md); skip with a message on a fresh clone rather than
# dying mid-run.
if [[ ! -d "$repo_root/../leandb-http" ]]; then
  echo "skipping dashboard checks: $repo_root/../leandb-http is missing (see RELEASING.md)"
else
  (
    cd examples/dashboard
    lake build
    .lake/build/bin/dashboard
  )
fi

# scaffold round trip: leandb new against this checkout builds and passes its tests
(
  new_dir=$(mktemp -d /tmp/leandb-new.XXXXXX)
  rm -rf "$new_dir"
  .lake/build/bin/leandb new scaffold_check --out "$new_dir" --leandb-path "$repo_root"
  if ! cmp -s lean-toolchain "$new_dir/lean-toolchain"; then
    echo "release check failed: scaffolded lean-toolchain differs from root" >&2
    exit 1
  fi
  (cd "$new_dir" && lake build && .lake/build/bin/scaffold_check_tests)
  if .lake/build/bin/leandb new scaffold_check --out "$new_dir" --leandb-path "$repo_root" >/dev/null 2>&1; then
    echo "release check failed: second scaffold into the same directory should fail" >&2
    exit 1
  fi
  rm -rf "$new_dir"
)

# HTTP smoke: tickets over serve --http answers the typed routes and /rpc
(
  cd examples/tickets
  http_db=$(mktemp /tmp/leandb-http.XXXXXX)
  rm -f "$http_db"
  .lake/build/bin/tickets --db "$http_db" serve --http 7433 --auth-token release-check >/dev/null 2>&1 &
  http_pid=$!
  sleep 2
  ok=1
  # the token gate: healthz open, everything else 401 without the bearer
  curl -sf http://127.0.0.1:7433/healthz | grep -q '"ok":true' || ok=0
  code=$(curl -s -o /dev/null -w '%{http_code}' http://127.0.0.1:7433/version)
  [[ "$code" == "401" ]] || ok=0
  curl() { command curl -H 'Authorization: Bearer release-check' "$@"; }
  curl -sf -X POST http://127.0.0.1:7433/seed | grep -q '"seeded":true' || ok=0
  curl -sf http://127.0.0.1:7433/query/slaBreached/1700000000 | grep -q '"ok":true' || ok=0
  curl -sf -X POST http://127.0.0.1:7433/rpc -d '["rows","ticket","--limit","1"]' | grep -q '"count":1' || ok=0
  code=$(curl -s -o /dev/null -w '%{http_code}' -H 'X-LeanDb-Fingerprint: stale' http://127.0.0.1:7433/version)
  [[ "$code" == "409" ]] || ok=0
  unset -f curl
  kill "$http_pid" 2>/dev/null || true
  wait "$http_pid" 2>/dev/null || true
  rm -f "$http_db"
  if [[ "$ok" != 1 ]]; then
    echo "release check failed: tickets serve --http smoke test failed" >&2
    exit 1
  fi
)

# MCP smoke: tools/list names a table verb and a query; tools/call runs one
(
  cd examples/tickets
  mcp_db=$(mktemp /tmp/leandb-mcp.XXXXXX)
  rm -f "$mcp_db"
  out=$(printf '%s\n' \
    '{"jsonrpc":"2.0","id":1,"method":"initialize","params":{"protocolVersion":"2025-06-18"}}' \
    '{"jsonrpc":"2.0","id":2,"method":"tools/list"}' \
    '{"jsonrpc":"2.0","id":3,"method":"tools/call","params":{"name":"seed","arguments":{}}}' \
    '{"jsonrpc":"2.0","id":4,"method":"tools/call","params":{"name":"query_slaBreached","arguments":{"now":1700000000}}}' \
    | .lake/build/bin/tickets --db "$mcp_db" serve --mcp)
  rm -f "$mcp_db"
  if [[ "$out" != *'"name":"rows_ticket"'* || "$out" != *'"name":"query_slaBreached"'* || "$out" != *'"isError":false'* ]]; then
    echo "release check failed: tickets serve --mcp smoke test failed" >&2
    exit 1
  fi
)

# host smoke: two bases under one port
(
  host_db=$(mktemp -d /tmp/leandb-host.XXXXXX)
  .lake/build/bin/leandb host --port 7434 \
    "tickets=examples/tickets/.lake/build/bin/tickets,--db,$host_db/t.sqlite" \
    "eats=examples/eats/.lake/build/bin/eats,--db,$host_db/e.sqlite" >/dev/null 2>&1 &
  host_pid=$!
  sleep 3
  ok=1
  curl -sf http://127.0.0.1:7434/bases | grep -q '"name":"eats"' || ok=0
  curl -sf -X POST http://127.0.0.1:7434/bases/eats/seed | grep -q '"seeded":true' || ok=0
  curl -sf http://127.0.0.1:7434/bases/eats/query/openFor/tiramisu/fri/21:30 | grep -q '"ok":true' || ok=0
  curl -sf http://127.0.0.1:7434/bases/tickets/version | grep -q '"code_fingerprint"' || ok=0
  kill "$host_pid" 2>/dev/null || true
  wait "$host_pid" 2>/dev/null || true
  pkill -f "$host_db" 2>/dev/null || true
  rm -rf "$host_db"
  if [[ "$ok" != 1 ]]; then
    echo "release check failed: leandb host smoke test failed" >&2
    exit 1
  fi
)

(
  cd examples/legacy
  lake build
  .lake/build/bin/legacy_tests
  schema_json=$(.lake/build/bin/legacy schema)
  if [[ "$schema_json" != *'"ok":true'* ]]; then
    echo "release check failed: legacy schema smoke test failed" >&2
    exit 1
  fi
)

import_dir=$(mktemp -d /tmp/leandb-release-check.XXXXXX)
trap 'rm -rf "$import_dir"' EXIT

.lake/build/bin/leandb import-sqlite examples/import-fixture/legacy.db \
  --name release_fixture \
  --out "$import_dir" \
  --require-path "$repo_root" \
  --db-path data/legacy.db

test -f "$import_dir/ReleaseFixture/Entities.lean"
test -f "$import_dir/import-report.json"
cmp -s lean-toolchain "$import_dir/lean-toolchain"

(
  cd "$import_dir"
  lake build
  schema_json=$(.lake/build/bin/release_fixture schema)
  if [[ "$schema_json" != *'"ok":true'* ]]; then
    echo "release check failed: generated package schema smoke test failed" >&2
    exit 1
  fi
)

if .lake/build/bin/leandb import-sqlite examples/import-fixture/legacy.db \
    --name release_fixture \
    --out "$import_dir" \
    --require-path "$repo_root" \
    --db-path data/legacy.db >/dev/null 2>&1; then
  echo "release check failed: importer overwrote an existing generated package" >&2
  exit 1
fi

git diff --check
echo "LeanDB release checks passed"
