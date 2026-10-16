#!/usr/bin/env python3
"""Run only against an already-built native binary; no cloud or build actions."""
import concurrent.futures
import contextlib
import json
import os
from pathlib import Path
import socket
import sqlite3
import subprocess
import sys
import tempfile
import time
import urllib.error
import urllib.request


TOKEN = "cf-native-smoke-only"


def encode(value):
    return json.dumps(value, separators=(",", ":"))


@contextlib.contextmanager
def server(binary, db):
    with socket.socket() as sock:
        sock.bind(("127.0.0.1", 0))
        port = sock.getsockname()[1]
    with db.with_suffix(".server.log").open("ab") as log:
        proc = subprocess.Popen(
            [str(binary), "--db", str(db), "serve", "--http", str(port),
             "--bind", "127.0.0.1"],
            env={**os.environ, "LEANDB_TOKEN": TOKEN}, stdout=log, stderr=log,
        )
        url = f"http://127.0.0.1:{port}"
        try:
            for _ in range(150):
                if proc.poll() is not None:
                    raise AssertionError(f"native exited; inspect {db.with_suffix('.server.log')}")
                try:
                    with urllib.request.urlopen(url + "/healthz", timeout=1) as response:
                        assert json.load(response) == {"ok": True}
                    break
                except (OSError, urllib.error.URLError):
                    time.sleep(0.1)
            else:
                raise AssertionError("native did not become ready")
            yield url
        finally:
            if proc.poll() is None:
                proc.terminate()
                try:
                    proc.wait(timeout=5)
                except subprocess.TimeoutExpired:
                    proc.kill()
                    proc.wait(timeout=5)


def query(url, name, args, token=TOKEN):
    request = urllib.request.Request(
        url + "/query/" + name, data=encode({"args": args}).encode(),
        headers={"Content-Type": "application/json", "Authorization": "Bearer " + token},
    )
    with urllib.request.urlopen(request, timeout=15) as response:
        assert response.status == 200
        body = json.load(response)
    assert body.get("ok") is True and "result" in body, body
    return body["result"]


def envelope(seq, actor, kind, tenant, key="shared", **operand):
    return encode({"seq": seq, "actor": actor, "requestId": f"smoke-{seq}",
                   "command": {"type": kind, "tenant": tenant, "key": key, **operand}})


def snapshot(url, actor="alice", tenant="alpha"):
    return query(url, "snapshot", [encode({"actor": actor, "tenant": tenant})])


def expect_failure(seq, code):
    return {"ok": False, "seq": seq, "code": code}


def main():
    if len(sys.argv) != 2:
        raise SystemExit("usage: python3 smoke.py /absolute/path/to/cf-native")
    binary = Path(sys.argv[1]).resolve(strict=True)
    root = Path(tempfile.mkdtemp(prefix="cf-native-smoke-"))
    print(f"smoke artifacts: {root}", flush=True)
    db = root / "state.sqlite"
    receipts = []

    with server(binary, db) as url:
        assert query(url, "status", []) == {"ok": True, "lastSeq": 0, "schemaVersion": "cf-v1"}
        assert snapshot(url) == {"ok": True, "items": [], "sum": 0, "count": 0}
        try:
            query(url, "status", [], token="wrong-synthetic-token")
            raise AssertionError("unauthenticated query accepted")
        except urllib.error.HTTPError as error:
            assert error.code == 401

        def apply(raw, expected):
            result = query(url, "apply", [raw])
            assert result == expected, (result, expected)
            receipts.append((raw, result))
            return result

        raw1 = envelope(1, "alice", "create", "alpha", value=10)
        apply(raw1, {"ok": True, "seq": 1, "value": 10})
        # Same key in a different tenant is legal; same composite key is not.
        apply(envelope(2, "bob", "create", "beta", value=20), {"ok": True, "seq": 2, "value": 20})
        apply(envelope(3, "alice", "create", "alpha", value=99), expect_failure(3, "duplicate"))
        apply(envelope(4, "alice", "increment", "alpha", delta=5), {"ok": True, "seq": 4, "value": 15})
        rollback = envelope(5, "alice", "rollback", "alpha", delta=100)
        apply(rollback, expect_failure(5, "rolled_back"))
        apply(envelope(6, "alice", "increment", "beta", delta=100), expect_failure(6, "forbidden"))
        apply(envelope(7, "alice", "increment", "alpha", key="missing", delta=1), expect_failure(7, "not_found"))
        apply(envelope(8, "alice", "create", "alpha", value="10"), expect_failure(8, "invalid"))
        apply(envelope(9, "alice", "create", "alpha", key="a", value=-2), {"ok": True, "seq": 9, "value": -2})
        assert query(url, "apply", [raw1]) == receipts[0][1]
        assert query(url, "apply", [rollback]) == expect_failure(5, "rolled_back")
        assert query(url, "apply", [raw1 + " "]) == expect_failure(1, "sequence_conflict")
        assert query(url, "apply", [envelope(11, "alice", "increment", "alpha", delta=1)]) == expect_failure(11, "sequence_gap")
        assert query(url, "apply", ["{"]) == expect_failure(0, "invalid")
        assert query(url, "apply", [envelope(0, "alice", "create", "alpha", value=1)]) == expect_failure(0, "invalid")
        assert snapshot(url, "alice", "beta") == {"ok": False, "code": "forbidden"}
        assert snapshot(url, "bob", "alpha") == {"ok": False, "code": "forbidden"}

        raw10 = envelope(10, "alice", "increment", "alpha", delta=1)
        expected10 = {"ok": True, "seq": 10, "value": 16}
        with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:
            results = list(pool.map(lambda _: query(url, "apply", [raw10]), range(8)))
        assert all(result == expected10 for result in results)
        receipts.append((raw10, expected10))
        # Missing operands and arithmetic overflow consume failure receipts.
        apply(envelope(11, "alice", "increment", "alpha"), expect_failure(11, "invalid"))
        apply(envelope(12, "alice", "increment", "alpha", delta=9223372036854775807), expect_failure(12, "invalid"))
        expected_alpha = {"ok": True, "items": [{"key": "a", "value": -2}, {"key": "shared", "value": 16}], "sum": 14, "count": 2}
        expected_beta = {"ok": True, "items": [{"key": "shared", "value": 20}], "sum": 20, "count": 1}
        assert snapshot(url) == expected_alpha
        assert snapshot(url, "bob", "beta") == expected_beta
        assert query(url, "status", [])["lastSeq"] == len(receipts)

        request = urllib.request.Request(url + "/tables/counter", headers={"Authorization": "Bearer " + TOKEN})
        try:
            urllib.request.urlopen(request, timeout=5)
            raise AssertionError("generic row reads bypass policy")
        except urllib.error.HTTPError as error:
            assert error.code == 403

    with sqlite3.connect(f"file:{db}?mode=ro", uri=True) as conn:
        stored = conn.execute("SELECT seq, envelope, result FROM applied ORDER BY seq").fetchall()
        assert len(stored) == len(receipts)
        for (seq, raw, result), (expected_raw, expected_result) in zip(stored, receipts):
            assert seq == expected_result["seq"] and raw == expected_raw
            assert json.loads(result) == expected_result
        # Inspect actual SQLite uniqueness, not merely application duplicate checks.
        def unique_columns(table):
            columns = []
            for index in conn.execute(f'PRAGMA index_list("{table}")').fetchall():
                if index[2]:
                    quoted = '"' + index[1].replace('"', '""') + '"'
                    columns.append(tuple(row[2] for row in conn.execute(f"PRAGMA index_info({quoted})")))
            return columns
        assert ("tenant", "key") in unique_columns("counter")
        assert ("seq",) in unique_columns("applied")

    # Restart after terminate() (SIGTERM; kill only on timeout) must retain receipts.
    with server(binary, db) as url:
        assert snapshot(url) == expected_alpha
        assert snapshot(url, "bob", "beta") == expected_beta
        for raw, expected in receipts:
            assert query(url, "apply", [raw]) == expected
        assert query(url, "status", [])["lastSeq"] == len(receipts)

    # Emulate loss of the native filesystem, followed by ordered journal replay.
    with server(binary, root / "replayed.sqlite") as url:
        assert query(url, "status", [])["lastSeq"] == 0
        for raw, expected in receipts:
            assert query(url, "apply", [raw]) == expected
        assert snapshot(url) == expected_alpha
        assert snapshot(url, "bob", "beta") == expected_beta
        assert query(url, "status", [])["lastSeq"] == len(receipts)

    print(f"PASS: native fixture smoke; {len(receipts)} persisted/replayed receipts")


if __name__ == "__main__":
    main()
