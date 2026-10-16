#!/usr/bin/env python3
"""Independent stdlib-only black-box checks for ../PROTOCOL.md (cf-v1)."""

from __future__ import annotations

import argparse
import concurrent.futures
import datetime as dt
import http.client
import json
import math
import os
from pathlib import Path
import re
import socket
import tempfile
import threading
import time
import urllib.error
import urllib.parse
import urllib.request
import uuid


SCHEMA = "cf-v1"
MAX_REQUESTS = 999
CONCURRENCY = 8
RETRY_SECONDS = 120.0
REQUEST_TIMEOUT = 15.0
MAX_BODY = 256 * 1024
TRANSIENT = {408, 425, 429, 500, 502, 503, 504}
TOKEN_NAMES = ("TOKEN_A", "TOKEN_B", "ADMIN_TOKEN")
ACTORS = {"alice": "alpha", "bob": "beta"}


def timestamp():
    return dt.datetime.now(dt.timezone.utc).isoformat(timespec="milliseconds")


def integer(value):
    return isinstance(value, int) and not isinstance(value, bool)


class SetupError(Exception):
    pass


class AssertionFailure(Exception):
    pass


class RunnerError(Exception):
    pass


class Redactor:
    def __init__(self):
        self.secrets = []

    def add(self, values):
        variants = set(self.secrets)
        for value in values:
            if isinstance(value, str) and value:
                variants.add(value)
                variants.add(urllib.parse.quote(value, safe=""))
                variants.add(json.dumps(value)[1:-1])
        self.secrets = sorted(variants, key=len, reverse=True)

    def clean(self, value):
        if isinstance(value, str):
            for secret in self.secrets:
                value = value.replace(secret, "[REDACTED]")
            return value
        if isinstance(value, dict):
            result = {}
            for key, item in value.items():
                safe_key = self.clean(str(key))
                normalized = re.sub(r"[^a-z0-9]", "", str(key).lower())
                sensitive = ("token" in normalized or "secret" in normalized
                             or "password" in normalized
                             or normalized in {"authorization", "cookie", "setcookie"})
                result[safe_key] = "[REDACTED]" if sensitive else self.clean(item)
            return result
        if isinstance(value, (list, tuple)):
            return [self.clean(item) for item in value]
        if isinstance(value, (int, float)) and not isinstance(value, bool):
            rendered = str(value)
            if isinstance(value, float) and not math.isfinite(value):
                return "[NONFINITE NUMBER]"
            if any(secret in rendered for secret in self.secrets):
                return "[REDACTED]"
        return value


def atomic_json(path, value, redactor):
    """Only sanitized content ever reaches disk, including temporary files."""
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    serialized = json.dumps(redactor.clean(value), indent=2, sort_keys=True,
                            ensure_ascii=True, allow_nan=False) + "\n"
    fd, temporary = tempfile.mkstemp(prefix="." + path.name + ".", dir=path.parent)
    try:
        with os.fdopen(fd, "w", encoding="utf-8") as output:
            output.write(serialized)
            output.flush()
            os.fsync(output.fileno())
        os.replace(temporary, path)
    finally:
        if os.path.exists(temporary):
            os.unlink(temporary)


class Evidence:
    def __init__(self, mode, run_id, redactor):
        self.redactor = redactor
        self.lock = threading.Lock()
        self.started = time.monotonic()
        self.data = {
            "format_version": 1, "protocol": SCHEMA, "run_id": run_id,
            "mode": mode, "started_at": timestamp(), "outcome": "running",
            "limits": {"requests": MAX_REQUESTS, "concurrency": CONCURRENCY,
                       "retry_window_seconds": RETRY_SECONDS,
                       "request_timeout_seconds": REQUEST_TIMEOUT},
            "assertions": [], "requests": [], "snapshots": [], "events": [],
            "failures": [],
        }

    def append(self, section, value):
        with self.lock:
            self.data[section].append(self.redactor.clean(value))

    def event(self, name, **details):
        self.append("events", {"at": timestamp(), "name": name, **details})

    def check(self, name, condition, expected, actual):
        passed = bool(condition)
        self.append("assertions", {
            "at": timestamp(), "name": name, "passed": passed,
            "expected": expected, "actual": actual,
        })
        if not passed:
            raise AssertionFailure(name)

    def finish(self, outcome, client):
        self.data.update({
            "outcome": outcome, "finished_at": timestamp(),
            "duration_ms": round((time.monotonic() - self.started) * 1000, 3),
            "request_count": client.count if client else 0,
            "previous_request_count": client.previous_count if client else 0,
            "total_request_count": client.previous_count + client.count if client else 0,
            "observed_max_concurrency": client.peak if client else 0,
        })
        self.data["requests"].sort(key=lambda row: row["number"])
        self.data["assertion_counts"] = {
            "passed": sum(row["passed"] for row in self.data["assertions"]),
            "failed": sum(not row["passed"] for row in self.data["assertions"]),
        }


class NoRedirects(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, req, fp, code, msg, headers, newurl):
        return None


class Client:
    def __init__(self, base_url, credentials, evidence):
        self.base_url = base_url
        self.credentials = credentials
        self.evidence = evidence
        self.semaphore = threading.BoundedSemaphore(CONCURRENCY)
        self.lock = threading.Lock()
        self.local = threading.local()
        self.count = self.active = self.peak = 0
        self.previous_count = 0

    def opener(self):
        if not hasattr(self.local, "opener"):
            # Do not forward bearer credentials on redirects or inherit proxy settings.
            self.local.opener = urllib.request.build_opener(
                urllib.request.ProxyHandler({}), NoRedirects())
        return self.local.opener

    def request(self, method, path, scenario, actor="alice", body=None,
                schema=None, timeout=REQUEST_TIMEOUT, raw=None, content_type=None):
        with self.semaphore:
            with self.lock:
                if self.previous_count + self.count >= MAX_REQUESTS:
                    raise RunnerError("request_budget_exhausted")
                self.count += 1
                number = self.count
                self.active += 1
                self.peak = max(self.peak, self.active)
            start = time.monotonic()
            record = {
                "number": number, "scenario": scenario, "method": method,
                "path": path, "credential_role": actor or "anonymous",
                "started_at": timestamp(), "request_body": body,
            }
            response = {"status": None, "json": None, "transport_error": None}
            try:
                headers = {"Accept": "application/json", "User-Agent": "LeanDB-Cloudflare-Experiment/1.0"}
                if actor:
                    headers["Authorization"] = "Bearer " + self.credentials[actor]
                if schema is not None:
                    headers["X-Experiment-Schema"] = schema
                    record["schema_header"] = schema
                data = raw
                if raw is not None:
                    record["request_body"] = {"raw_bytes": len(raw)}
                elif body is not None:
                    data = json.dumps(body, separators=(",", ":")).encode("utf-8")
                if data is not None:
                    headers["Content-Type"] = content_type or "application/json"
                req = urllib.request.Request(self.base_url + path, data=data,
                                             headers=headers, method=method)
                try:
                    stream = self.opener().open(req, timeout=max(0.001, timeout))
                except urllib.error.HTTPError as error:
                    stream = error
                with stream:
                    response["status"] = stream.code
                    # read1 returns after one buffered/socket read. Checking the
                    # deadline between chunks prevents an endless trickle body.
                    chunks, size = [], 0
                    while size <= MAX_BODY:
                        remaining = timeout - (time.monotonic() - start)
                        if remaining <= 0:
                            raise TimeoutError()
                        source = stream.fp if isinstance(stream, urllib.error.HTTPError) else stream
                        if source.fp is not None:
                            # urllib exposes HTTPResponse; tighten its underlying
                            # socket timeout to the remaining whole-request budget.
                            source.fp.raw._sock.settimeout(remaining)
                        chunk = stream.read1(min(16384, MAX_BODY + 1 - size))
                        if not chunk:
                            break
                        chunks.append(chunk)
                        size += len(chunk)
                    payload = b"".join(chunks)
                response["body_bytes"] = len(payload)
                if len(payload) > MAX_BODY:
                    response["body_error"] = "response_exceeds_capture_limit"
                elif payload:
                    try:
                        response["json"] = json.loads(
                            payload.decode("utf-8"),
                            parse_constant=lambda value: (_ for _ in ()).throw(ValueError()))
                    except (UnicodeError, ValueError, RecursionError):
                        # Unparsed bodies might contain credentials; never capture raw text.
                        response["body_error"] = "invalid_json_raw_body_omitted"
                else:
                    response["body_error"] = "empty_body"
            except (urllib.error.URLError, http.client.HTTPException, TimeoutError, socket.timeout,
                    OSError, ValueError) as error:
                # Exception messages can contain URLs/headers. Keep only their type.
                response["transport_error"] = type(error).__name__
            finally:
                record.update(response)
                record["finished_at"] = timestamp()
                record["duration_ms"] = round((time.monotonic() - start) * 1000, 3)
                self.evidence.append("requests", record)
                with self.lock:
                    self.active -= 1
            return response

    def retry(self, method, path, scenario, *, setup=False, deadline=None, **kwargs):
        deadline = deadline or (time.monotonic() + RETRY_SECONDS)
        delay = 0.5
        while True:
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                if setup:
                    raise SetupError("bootstrap_retry_deadline_exceeded")
                self.evidence.check(scenario + ": retry deadline", False,
                                    "response within 120 seconds", "deadline exceeded")
            response = self.request(method, path, scenario,
                                    timeout=min(REQUEST_TIMEOUT, remaining), **kwargs)
            if time.monotonic() >= deadline:
                if setup:
                    raise SetupError("bootstrap_retry_deadline_exceeded")
                self.evidence.check(scenario + ": retry deadline", False,
                                    "response within 120 seconds", "deadline exceeded")
            if response["transport_error"] is None and response["status"] not in TRANSIENT:
                return response
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                continue
            time.sleep(min(delay, remaining))
            delay = min(delay * 2, 5.0)


def validate_base_url(value):
    try:
        parts = urllib.parse.urlsplit(value)
        port = parts.port
    except ValueError:
        raise SetupError("invalid_base_url") from None
    if (parts.scheme not in {"http", "https"} or not parts.hostname
            or parts.username is not None or parts.password is not None
            or parts.query or parts.fragment or any(char.isspace() for char in value)):
        raise SetupError("base_url_must_have_no_credentials_query_or_fragment")
    if parts.scheme == "http" and parts.hostname not in {"localhost", "127.0.0.1", "::1"}:
        raise SetupError("remote_base_url_requires_https")
    if port == 0:
        raise SetupError("invalid_base_url_port")
    return value.rstrip("/")


def load_credentials(path, redactor):
    if path:
        try:
            values = json.loads(Path(path).read_text(encoding="utf-8"))
        except (OSError, UnicodeError, ValueError):
            raise SetupError("cannot_read_credentials_json") from None
        if not isinstance(values, dict):
            raise SetupError("credentials_file_must_be_an_object")
    else:
        values = {name: os.environ.get(name) for name in TOKEN_NAMES}
    # Register even malformed credential values before any possible diagnostic.
    redactor.add(values.values())
    if any(not isinstance(values.get(name), str) or not values[name]
           or any(ord(char) < 33 or ord(char) > 126 for char in values[name])
           for name in TOKEN_NAMES):
        raise SetupError("three_nonempty_ascii_bearer_credentials_required")
    if len({values[name] for name in TOKEN_NAMES}) != 3:
        raise SetupError("actor_and_admin_credentials_must_be_distinct")
    return dict(zip(("alice", "bob", "admin"), (values[name] for name in TOKEN_NAMES)))


class Probes:
    def __init__(self, client, evidence, checkpoint_path, run_id):
        self.client = client
        self.evidence = evidence
        self.checkpoint_path = checkpoint_path
        self.run_id = run_id
        self.origin_run_id = run_id
        self.prefix = "probe-" + run_id
        self.models = {"durable": {}, "ephemeral": {}}
        self.receipts = []
        self.stage = "setup"
        self.checkpoint_written = False
        self.last_checkpoint = None

    def check(self, name, condition, expected, actual):
        self.evidence.check(self.stage + ": " + name, condition, expected, actual)

    def http(self, response, status, name):
        self.check(name + " HTTP status", response["status"] == status
                   and response["transport_error"] is None, status, response)
        return response["json"]

    def json_object(self, value, name):
        self.check(name + " JSON object", isinstance(value, dict), "object", value)
        return value

    def status(self, mode, *, setup=False, previous_boot=None, actor="alice"):
        deadline = time.monotonic() + RETRY_SECONDS
        while True:
            response = self.client.retry("GET", f"/{mode}/status", self.stage,
                                         setup=setup, deadline=deadline, actor=actor)
            if setup and (response["status"] != 200 or response["transport_error"]):
                raise SetupError(mode + "_status_unavailable_or_credentials_rejected")
            value = self.json_object(self.http(response, 200, mode + " status"), "status")
            self.check("status schema", value.get("schemaVersion") == SCHEMA,
                       SCHEMA, value.get("schemaVersion"))
            for field in ("lastSeq", "journalCount"):
                self.check("status " + field, integer(value.get(field)) and value[field] >= 0,
                           "nonnegative integer", value.get(field))
            self.check("status bootId", isinstance(value.get("bootId"), str)
                       and bool(value["bootId"]), "nonempty container boot marker",
                       value.get("bootId"))
            if previous_boot is None or value["bootId"] != previous_boot:
                return value
            self.evidence.event("waiting_for_new_boot", mode=mode, status=value)
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                self.check("boot changed", False, "different bootId", value["bootId"])
            time.sleep(min(1.0, remaining))

    def snapshot(self, mode, actor, *, compare=True):
        tenant = ACTORS[actor]
        response = self.client.retry("POST", f"/{mode}/snapshot", self.stage,
                                     actor=actor, body={"tenant": tenant})
        value = response["json"]
        self.evidence.append("snapshots", {
            "at": timestamp(), "stage": self.stage, "mode": mode,
            "actor": actor, "tenant": tenant, "response": response,
        })
        self.json_object(self.http(response, 200, "snapshot"), "snapshot")
        self.check("snapshot success", value.get("ok") is True, True, value.get("ok"))
        items = value.get("items")
        self.check("snapshot items", isinstance(items, list), "list", items)
        valid = all(isinstance(item, dict) and isinstance(item.get("key"), str)
                    and integer(item.get("value")) for item in items)
        self.check("snapshot item schema", valid, "{key:string,value:integer}[]", items)
        keys = [item["key"] for item in items]
        self.check("snapshot keys unique and sorted", keys == sorted(set(keys)),
                   sorted(set(keys)), keys)
        expected_sum = sum(item["value"] for item in items)
        self.check("derived count", integer(value.get("count"))
                   and value["count"] == len(items), len(items), value.get("count"))
        self.check("derived sum", integer(value.get("sum"))
                   and value["sum"] == expected_sum, expected_sum, value.get("sum"))
        actual = {item["key"]: item["value"] for item in items}
        if compare:
            self.check(mode + " " + tenant + " exact contents",
                       actual == self.models[mode][actor], self.models[mode][actor], actual)
        else:
            self.models[mode][actor] = actual
        return value

    def snapshots(self, mode, *, compare=True):
        return {actor: self.snapshot(mode, actor, compare=compare) for actor in ACTORS}

    def command_body(self, actor, name, kind, key, **fields):
        return {"requestId": self.prefix + ":" + name,
                "command": {"type": kind, "tenant": ACTORS[actor], "key": key, **fields}}

    def send_command(self, mode, actor, body, *, once=False):
        call = self.client.request if once else self.client.retry
        return call("POST", f"/{mode}/command", self.stage, actor=actor, body=body)

    def result(self, response, *, value=None, error=None):
        result = self.json_object(self.http(response, 200, "native result"), "native result")
        self.check("native result sequence", integer(result.get("seq")) and result["seq"] > 0,
                   "positive integer", result.get("seq"))
        if error is None:
            self.check("native command succeeded", result.get("ok") is True, True, result)
            self.check("native value", integer(result.get("value")) and result["value"] == value,
                       value, result.get("value"))
        else:
            self.check("native domain rejection", result.get("ok") is False
                       and result.get("code") == error,
                       {"ok": False, "code": error}, result)
        return result

    def mutate(self, mode, actor, name, kind, key, amount, *, remember=False):
        field = "value" if kind == "create" else "delta"
        body = self.command_body(actor, name, kind, key, **{field: amount})
        expected = amount if kind == "create" else self.models[mode][actor][key] + amount
        result = self.result(self.send_command(mode, actor, body), value=expected)
        self.models[mode][actor][key] = expected
        if remember:
            self.receipts.append({"actor": actor, "body": body, "result": result})
        return body, result

    def domain_failure(self, actor, body, code):
        before = self.status("durable")
        result = self.result(self.send_command("durable", actor, body), error=code)
        # Failure must be recorded in native Applied after its mutation rolls
        # back, rather than looking like a gateway-only denial with a stale seq.
        after = self.status("durable")
        self.check("failed command native sequence", result["seq"] == before["lastSeq"] + 1,
                   before["lastSeq"] + 1, result["seq"])
        for field in ("lastSeq", "journalCount"):
            self.check("one recorded domain failure " + field, after[field] == before[field] + 1,
                       before[field] + 1, after[field])
        self.snapshots("durable")

    def admin(self, mode, action, body=None):
        method = "GET" if action == "journal" else "POST"
        # Never transparently repeat destructive/fault-injection admin calls.
        response = self.client.request(method, f"/{mode}/admin/{action}", self.stage,
                                       actor="admin", body=body)
        return self.http(response, 200, "admin " + action)

    def journal_count(self):
        body = self.admin("durable", "journal")
        count = body if integer(body) else None
        if isinstance(body, dict):
            count = body.get("count", body.get("journalCount"))
            self.check("journal exposes count only", set(body) <= {"count", "journalCount", "ok"},
                       "count metadata without journal entries", list(body))
        self.check("journal count", integer(count) and count >= 0, "nonnegative integer", body)
        return count

    def state_unchanged(self, before, after):
        for field in ("lastSeq", "journalCount"):
            self.check("unchanged " + field, after[field] == before[field], before[field], after[field])

    def access_checks(self):
        self.stage = "authentication and schema"
        for mode in ("durable", "ephemeral"):
            body = self.command_body("alice", "must-not-create-" + mode, "create",
                                     self.prefix + "-unauthorized", value=999)
            for actor in (None, "invalid"):
                for method, route, payload in (
                    ("GET", "status", None), ("POST", "snapshot", {"tenant": "alpha"}),
                    ("POST", "command", body),
                ):
                    self.http(self.client.request(method, f"/{mode}/{route}", self.stage,
                                                  actor=actor, body=payload), 401,
                              mode + " " + route + " unauthenticated")
            for method, route, payload in (
                ("GET", "status", None), ("POST", "snapshot", {"tenant": "alpha"}),
                ("POST", "command", body),
            ):
                self.http(self.client.request(method, f"/{mode}/{route}", self.stage,
                                              body=payload, schema="incompatible-probe-schema"),
                          409, mode + " " + route + " schema mismatch")
            self.http(self.client.request("GET", f"/{mode}/status", self.stage, schema=SCHEMA),
                      200, "explicit compatible schema")

        self.stage = "protected admin routes"
        routes = []
        for mode in ("durable", "ephemeral"):
            routes.extend((method, f"/{mode}/admin/{action}", None)
                          for method, action in (("POST", "inject"), ("POST", "destroy"),
                                                 ("GET", "journal")))
        routes.extend(("POST", f"/durable/admin/{action}", b"" if action == "workspace" else None)
                      for action in ("workspace", "exec", "call", "publish"))
        routes.append(("GET", "/admin/artifact", None))
        for actor in (None, "alice", "bob"):
            for method, path, raw in routes:
                response = self.client.request(method, path, self.stage, actor=actor,
                                               body={} if method == "POST" else None,
                                               raw=raw,
                                               content_type="application/gzip" if raw is not None else None)
                self.http(response, 401, path + " denied for " + (actor or "anonymous"))
        for mode in ("durable", "ephemeral"):
            self.snapshots(mode)

    def basic_semantics(self):
        self.stage = "create read increment"
        key = self.prefix + "-main"
        for actor, initial in (("alice", 10), ("bob", 20)):
            self.mutate("durable", actor, "create-" + actor, "create", key, initial)
            self.snapshot("durable", actor)
        self.mutate("durable", "alice", "increment", "increment", key, 3)
        self.snapshots("durable")

        self.stage = "native tenant read and write policy"
        for actor, other_tenant in (("alice", "beta"), ("bob", "alpha")):
            response = self.client.retry("POST", "/durable/snapshot", self.stage,
                                         actor=actor, body={"tenant": other_tenant})
            value = self.json_object(self.http(response, 200, "cross tenant read"), "rejection")
            self.check("cross tenant read forbidden", value.get("ok") is False
                       and value.get("code") == "forbidden"
                       and not any(field in value for field in ("items", "sum", "count")),
                       {"ok": False, "code": "forbidden"}, value)
            body = self.command_body(actor, "cross-write-" + actor, "increment", key, delta=900)
            body["command"]["tenant"] = other_tenant
            self.domain_failure(actor, body, "forbidden")
        self.snapshots("durable")

        self.stage = "unique constraint and rollback"
        duplicate = self.command_body("alice", "duplicate", "create", key, value=999)
        self.domain_failure("alice", duplicate, "duplicate")
        self.snapshot("durable", "alice")
        rollback = self.command_body("alice", "rollback", "rollback", key, delta=100)
        self.domain_failure("alice", rollback, "rolled_back")
        self.snapshots("durable")

        self.stage = "request idempotency and conflict"
        body, original = self.mutate("durable", "alice", "retry", "increment", key, 7, remember=True)
        before = self.status("durable")
        repeated = self.result(self.send_command("durable", "alice", body), value=20)
        self.check("identical retry receipt", repeated == original, original, repeated)
        reordered = {"command": dict(reversed(list(body["command"].items()))),
                     "requestId": body["requestId"]}
        repeated = self.result(self.send_command("durable", "alice", reordered), value=20)
        self.check("canonical command retry receipt", repeated == original, original, repeated)
        conflict = {"requestId": body["requestId"], "command": {**body["command"], "delta": 99}}
        self.http(self.send_command("durable", "alice", conflict), 409, "conflicting requestId")
        self.state_unchanged(before, self.status("durable"))
        self.snapshots("durable")
        # The same requestId belongs to a different idempotency scope for bob.
        scoped = {"requestId": body["requestId"],
                  "command": {"type": "increment", "tenant": "beta", "key": key, "delta": 2}}
        result = self.result(self.send_command("durable", "bob", scoped), value=22)
        self.models["durable"]["bob"][key] = 22
        self.receipts.append({"actor": "bob", "body": scoped, "result": result})
        self.snapshots("durable")

    def concurrent_count(self):
        self.stage = "concurrent exact count 8 x 5"
        key = self.prefix + "-concurrent"
        self.mutate("durable", "alice", "concurrent-create", "create", key, 0)
        before = self.status("durable")
        barrier = threading.Barrier(CONCURRENCY)

        def worker(worker_number):
            barrier.wait(timeout=30)
            results = []
            for iteration in range(5):
                body = self.command_body("alice", f"parallel-{worker_number}-{iteration}",
                                         "increment", key, delta=1)
                response = self.send_command("durable", "alice", body)
                value = self.json_object(self.http(response, 200, "concurrent command"), "receipt")
                self.check("concurrent receipt", value.get("ok") is True
                           and integer(value.get("value")) and integer(value.get("seq")),
                           "successful integer value and seq", value)
                results.append(value)
            return results

        results, errors = [], []
        worker_error = False
        with concurrent.futures.ThreadPoolExecutor(max_workers=CONCURRENCY) as executor:
            futures = [executor.submit(worker, number) for number in range(CONCURRENCY)]
            for future in futures:
                try:
                    results.extend(future.result())
                except Exception as error:
                    errors.append(type(error).__name__)
                    worker_error = worker_error or not isinstance(error, AssertionFailure)
        self.models["durable"]["alice"][key] = 40
        if worker_error:
            self.evidence.event("concurrent_worker_errors", errors=errors)
            raise RunnerError("concurrent_worker_error")
        # Capture the actual resulting state even if a worker assertion failed.
        self.snapshots("durable")
        self.check("all concurrent workers completed", not errors, [], errors)
        values = sorted(result["value"] for result in results)
        self.check("40 serialized increment receipts", values == list(range(1, 41)), list(range(1, 41)), values)
        sequences = [result["seq"] for result in results]
        self.check("40 distinct native sequences", len(set(sequences)) == 40, 40, len(set(sequences)))
        after = self.status("durable")
        self.check("40 new applied entries", after["lastSeq"] == before["lastSeq"] + 40,
                   before["lastSeq"] + 40, after["lastSeq"])
        self.check("40 new journal entries", after["journalCount"] == before["journalCount"] + 40,
                   before["journalCount"] + 40, after["journalCount"])

    def save_checkpoint(self, status, snapshots, phase, *, ready=False):
        checkpoint = {
            "format_version": 1, "protocol": SCHEMA, "base_url": self.client.base_url,
            "origin_run_id": self.origin_run_id, "last_run_id": self.run_id,
            "request_count": self.client.previous_count + self.client.count,
            "written_at": timestamp(), "phase": phase, "ready_for_redeploy": ready,
            "durable": {"status": status, "snapshots": snapshots, "receipts": self.receipts},
        }
        atomic_json(self.checkpoint_path, checkpoint, self.evidence.redactor)
        self.last_checkpoint = checkpoint
        self.checkpoint_written = True
        self.evidence.event("checkpoint_written", phase=phase, ready_for_redeploy=ready)

    def invalidate_checkpoint(self):
        if self.last_checkpoint is None:
            return
        checkpoint = {**self.last_checkpoint, "ready_for_redeploy": False,
                      "phase": "incomplete: " + self.stage, "written_at": timestamp(),
                      "last_run_id": self.run_id,
                      "request_count": self.client.previous_count + self.client.count}
        atomic_json(self.checkpoint_path, checkpoint, self.evidence.redactor)
        self.checkpoint_written = True
        self.evidence.event("checkpoint_invalidated", phase=self.stage)

    def destroy_recover(self, mode, label):
        self.stage = label + " before destroy"
        before = self.status(mode)
        snapshots = self.snapshots(mode)
        if mode == "durable":
            count = self.journal_count()
            self.check("journal/status count agrees", count == before["journalCount"],
                       before["journalCount"], count)
            self.save_checkpoint(before, snapshots, label + " before destroy")
        self.stage = label + " destroy"
        result = self.json_object(self.admin(mode, "destroy", {}), "destroy response")
        self.check("destroy acknowledged", result.get("ok") is True, True, result)
        self.stage = label + " recovery"
        after = self.status(mode, previous_boot=before["bootId"])
        self.check("new container boot", after["bootId"] != before["bootId"],
                   "bootId differs from " + before["bootId"], after["bootId"])
        if mode == "ephemeral":
            self.models[mode] = {actor: {} for actor in ACTORS}
        restored = self.snapshots(mode)
        if mode == "durable":
            self.state_unchanged(before, after)
            self.save_checkpoint(after, restored, label + " recovered")
        else:
            self.check("ephemeral applied log lost", after["lastSeq"] == 0, 0, after["lastSeq"])
            self.evidence.event("ephemeral_negative_control", before=snapshots, after=restored)
        return after

    def retry_receipts(self, receipts):
        before = self.status("durable")
        for receipt in receipts:
            response = self.send_command("durable", receipt["actor"], receipt["body"])
            actual = self.http(response, 200, "persisted receipt retry")
            self.check("persisted original receipt", actual == receipt["result"], receipt["result"], actual)
        self.state_unchanged(before, self.status("durable"))
        self.snapshots("durable")

    def injection(self, point):
        self.stage = point + " injection and retry"
        key = self.prefix + "-main"
        before = self.status("durable")
        self.snapshots("durable")
        self.admin("durable", "inject", {"point": point})
        body = self.command_body("alice", point, "increment", key, delta=11)
        self.http(self.send_command("durable", "alice", body, once=True), 503,
                  "first command after " + point)
        expected = self.models["durable"]["alice"][key] + 11
        original = self.result(self.send_command("durable", "alice", body), value=expected)
        self.models["durable"]["alice"][key] = expected
        receipt = {"actor": "alice", "body": body, "result": original}
        self.receipts.append(receipt)
        repeated = self.result(self.send_command("durable", "alice", body), value=expected)
        self.check("fault retry original receipt", repeated == original, original, repeated)
        after = self.status("durable")
        for field in ("lastSeq", "journalCount"):
            self.check("fault applied once " + field, after[field] == before[field] + 1,
                       before[field] + 1, after[field])
        self.snapshots("durable")
        self.destroy_recover("durable", point + " subsequent destroy")
        self.stage = point + " persisted retry after destroy"
        self.retry_receipts([receipt])

    def full(self):
        self.stage = "bootstrap"
        health = self.client.retry("GET", "/health", self.stage, actor=None, setup=True)
        if health["status"] != 200:
            raise SetupError("health_endpoint_unavailable")
        self.json_object(self.http(health, 200, "public health"), "health metadata")
        initial_status = {}
        for mode in ("durable", "ephemeral"):
            initial_status[mode] = self.status(mode, setup=True)
            bob_status = self.status(mode, setup=True, actor="bob")
            self.state_unchanged(initial_status[mode], bob_status)
            self.snapshots(mode, compare=False)
        # Check admin credentials before executing the semantic experiments.
        admin = self.client.request("GET", "/durable/admin/journal", self.stage, actor="admin")
        if admin["status"] != 200 or admin["transport_error"]:
            raise SetupError("admin_credentials_or_journal_endpoint_unavailable")
        self.access_checks()
        for mode in ("durable", "ephemeral"):
            self.state_unchanged(initial_status[mode], self.status(mode))
        self.basic_semantics()
        self.concurrent_count()
        self.destroy_recover("durable", "durable persistence")
        self.stage = "original receipts after container loss"
        self.retry_receipts(self.receipts)

        self.stage = "ephemeral negative control seed"
        for actor, value in (("alice", 31), ("bob", 41)):
            self.mutate("ephemeral", actor, "ephemeral-" + actor, "create",
                        self.prefix + "-ephemeral", value)
        self.snapshots("ephemeral")
        self.destroy_recover("ephemeral", "ephemeral negative control")
        self.stage = "durable independent of ephemeral loss"
        self.snapshots("durable")
        for point in ("after-journal", "after-native"):
            self.injection(point)
        self.stage = "final durable checkpoint"
        snapshots = self.snapshots("durable")
        status = self.status("durable")
        count = self.journal_count()
        self.check("final journal count agrees", count == status["journalCount"], status["journalCount"], count)
        self.save_checkpoint(status, snapshots, "full complete", ready=True)

    def load_checkpoint(self):
        try:
            value = json.loads(Path(self.checkpoint_path).read_text(encoding="utf-8"))
            if (value["format_version"] != 1 or value["protocol"] != SCHEMA
                    or value["base_url"] != self.client.base_url
                    or value["ready_for_redeploy"] is not True
                    or not integer(value["request_count"])
                    or not (0 <= value["request_count"] <= MAX_REQUESTS)
                    or not isinstance(value["origin_run_id"], str)):
                raise ValueError()
            durable = value["durable"]
            status = durable["status"]
            if (status["schemaVersion"] != SCHEMA or not isinstance(status["bootId"], str)
                    or not status["bootId"] or any(not integer(status[field]) or status[field] < 0
                                                 for field in ("lastSeq", "journalCount"))):
                raise ValueError()
            for actor in ACTORS:
                snapshot = durable["snapshots"][actor]
                items = snapshot["items"]
                if (snapshot["ok"] is not True or not isinstance(items, list)
                        or any(not isinstance(item["key"], str) or not integer(item["value"])
                               for item in items)):
                    raise ValueError()
                model = {item["key"]: item["value"] for item in items}
                if (list(model) != sorted(model) or len(model) != len(items)
                        or not integer(snapshot["count"]) or snapshot["count"] != len(items)
                        or not integer(snapshot["sum"]) or snapshot["sum"] != sum(model.values())):
                    raise ValueError()
                self.models["durable"][actor] = model
            receipts = durable["receipts"]
            if not isinstance(receipts, list) or not (1 <= len(receipts) <= 20):
                raise ValueError()
            for receipt in receipts:
                actor, body, result = receipt["actor"], receipt["body"], receipt["result"]
                command = body["command"]
                if (actor not in ACTORS or not isinstance(body["requestId"], str)
                        or not body["requestId"] or command["tenant"] != ACTORS[actor]
                        or command["type"] != "increment" or not isinstance(command["key"], str)
                        or command["key"] not in self.models["durable"][actor]
                        or not integer(command["delta"]) or result["ok"] is not True
                        or not integer(result["seq"]) or not (0 < result["seq"] <= status["lastSeq"])
                        or not integer(result["value"])):
                    raise ValueError()
            self.receipts = receipts
            self.origin_run_id = value["origin_run_id"]
            self.client.previous_count = value["request_count"]
            self.last_checkpoint = value
        except (OSError, UnicodeError, ValueError, TypeError, KeyError, RecursionError):
            raise SetupError("checkpoint_missing_invalid_incomplete_or_endpoint_mismatch") from None
        return durable

    def redeploy_check(self):
        self.stage = "checkpoint validation"
        durable = self.load_checkpoint()  # All validation precedes any network call.
        self.stage = "external redeploy continuity"
        after = self.status("durable", setup=True)
        self.state_unchanged(durable["status"], after)
        self.snapshots("durable")
        self.evidence.event("external_redeploy_boot_observation",
                            previous_boot_id=durable["status"]["bootId"],
                            current_boot_id=after["bootId"],
                            changed=durable["status"]["bootId"] != after["bootId"])
        self.retry_receipts(self.receipts)
        self.destroy_recover("durable", "post redeploy forced recovery")
        self.stage = "post redeploy persisted receipts"
        self.retry_receipts(self.receipts)
        snapshots = self.snapshots("durable")
        status = self.status("durable")
        self.save_checkpoint(status, snapshots, "redeploy-check complete", ready=True)


def arguments():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("baseURL", help="experiment HTTPS origin, or local loopback HTTP URL")
    parser.add_argument("--mode", choices=("full", "redeploy-check"), default="full")
    parser.add_argument("--tokens-file", type=Path,
                        help="JSON file containing TOKEN_A, TOKEN_B, ADMIN_TOKEN; otherwise use environment")
    parser.add_argument("--checkpoint", type=Path, default=Path("checkpoint.json"))
    parser.add_argument("--evidence", type=Path, help="unique output JSON (default: artifacts/<run-id>-<mode>.json)")
    parser.add_argument("--execute", action="store_true",
                        help="explicitly authorize live requests and experiment container destruction")
    return parser.parse_args()


def main():
    args = arguments()
    if not args.execute:
        print("SETUP_ERROR: live execution requires --execute; no credentials read or requests sent.")
        return 2
    run_id = uuid.uuid4().hex
    redactor = Redactor()
    evidence = Evidence(args.mode, run_id, redactor)
    evidence_path = args.evidence or Path("artifacts") / (run_id + "-" + args.mode + ".json")
    client = probes = None
    exit_code, outcome = 3, "runner_error"
    try:
        credentials = load_credentials(args.tokens_file, redactor)
        base_url = validate_base_url(args.baseURL)
        paths = [evidence_path.resolve(), args.checkpoint.resolve()]
        if paths[0] == paths[1] or (args.tokens_file and args.tokens_file.resolve() in paths):
            raise SetupError("credential_checkpoint_and_evidence_paths_must_differ")
        if evidence_path.exists():
            raise SetupError("evidence_path_already_exists")
        if args.mode == "full" and args.checkpoint.exists():
            raise SetupError("full_requires_a_new_checkpoint_path")
        evidence.data["base_url"] = redactor.clean(base_url)
        credentials["invalid"] = "intentionally-invalid-" + run_id
        client = Client(base_url, credentials, evidence)
        probes = Probes(client, evidence, args.checkpoint, run_id)
        if args.mode == "full":
            probes.full()
        else:
            probes.redeploy_check()
        exit_code, outcome = 0, "passed"
    except SetupError as error:
        exit_code, outcome = 2, "setup_error"
        evidence.append("failures", {"at": timestamp(), "category": outcome, "reason": str(error)})
    except AssertionFailure as error:
        exit_code, outcome = 1, "assertion_failure"
        evidence.append("failures", {"at": timestamp(), "category": outcome, "reason": str(error)})
    except KeyboardInterrupt:
        exit_code, outcome = 130, "interrupted"
        evidence.append("failures", {"at": timestamp(), "category": outcome})
    except RunnerError as error:
        evidence.append("failures", {"at": timestamp(), "category": outcome,
                                     "reason": str(error)})
    except Exception as error:
        evidence.append("failures", {"at": timestamp(), "category": outcome,
                                     "reason": type(error).__name__})
    if probes and outcome != "passed":
        try:
            probes.invalidate_checkpoint()
        except Exception as error:
            exit_code, outcome = 3, "runner_error"
            evidence.append("failures", {"at": timestamp(), "category": outcome,
                                         "reason": "checkpoint_invalidation_" + type(error).__name__})
    evidence.data["last_stage"] = probes.stage if probes else "setup"
    evidence.data["checkpoint_written"] = bool(probes and probes.checkpoint_written)
    evidence.finish(outcome, client)
    try:
        # A setup mistake must never overwrite a credential file or existing evidence.
        unsafe = evidence_path.exists() or (args.tokens_file and
                 evidence_path.resolve() == args.tokens_file.resolve()) or (
                 evidence_path.resolve() == args.checkpoint.resolve())
        if unsafe:
            evidence_path = Path("artifacts") / (run_id + "-setup-error.json")
        atomic_json(evidence_path, evidence.data, redactor)
    except Exception:
        print("RUNNER_ERROR: could not write evidence; no response bodies printed.")
        return 3
    print(redactor.clean(outcome.upper() + ": " + str(evidence.data["request_count"])
                         + " requests; evidence=" + str(evidence_path)))
    return exit_code


if __name__ == "__main__":
    raise SystemExit(main())
