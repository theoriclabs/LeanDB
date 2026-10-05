#!/usr/bin/env python3
"""Gate for `LeanDb.Model` (the portable data model) and `LeanDb.Native` (it on SQLite).

1. The portable library builds alone, and its import closure is LeanDb.Model,
   LeanOntology and Lean only (no SQLite, no native LeanDB).
2. `leandb_model_tests`: the same programs in memory and on SQLite, and the model
   on SQLite (migrations, structured columns, represented fields, joins).
3. Negative fixtures: each must be rejected by the compiler for its reason.
"""
import os
from pathlib import Path
import subprocess

root = Path(__file__).resolve().parent.parent
env = dict(os.environ, LEAN_NUM_THREADS="2")

def run(command):
    subprocess.run(command, cwd=root, env=env, check=True)

run(["lake", "build", "LeanDbModel"])
closure = subprocess.run(["lake", "env", "lean", "-j", "2", "scripts/ModelClosure.lean"],
                         cwd=root, env=env, text=True, capture_output=True, check=False)
if closure.returncode != 0 or "all portable" not in closure.stdout:
    raise SystemExit("LeanDb.Model closure check failed\n" + closure.stdout + closure.stderr)
print(closure.stdout.strip().split(": ", 2)[-1], flush=True)

run(["lake", "build", "leandb_model_tests", "TestsModel"])
run([str(root / ".lake/build/bin/leandb_model_tests")])

fixtures = {
    # The model's declarations.
    "MissingConflictCase": "Missing cases:\n(Except.error Rsvp.Conflict.onePerGuest)",
    "ConstraintAfterUse": "must be declared before Person.insert",
    "PrivateFindBy": "Unknown constant `Rsvp.findBy`",
    "InternalSelect": "Unknown constant `Rsvp.select`",
    "ChangesExcludesField": "`date` is not a field of structure `Party.Changes`",
    "RepresentMissing": "failed to synthesize instance of type class\n  FieldType Opaque",
    "UnsupportedDependent": "monomorphic",
    "UnsupportedInherited": "inherited Domain record",
    "UnsupportedPayload": "payload-free",
    # Programs: read-only queries, scoped rows, typed references.
    "QueryWrite": "but is expected to have type\n  Query",
    "ScopeEscape": "Type mismatch\n  row\nhas type\n  Row Scope Party\nbut is expected to have type\n  Row Unit Party",
    "WrongFindId": "Application type mismatch",
    # The native evidence.
    "UniqueEvolution": "Missing cases:\n(LeanDb.InsertError.duplicate Account.Unique.byEmail",
    "WrongFieldStorage": "Tactic `rfl` failed",
    "WrongUniqueGetter": "Profile.byEmail.field.get",
    "UndeclaredUniqueKey": "forgedKey",
}
for name, expected in fixtures.items():
    result = subprocess.run(["lake", "env", "lean", "-j", "2", f"fixtures/model/{name}.lean"],
                            cwd=root, env=env, text=True, capture_output=True, check=False)
    diagnostic = result.stdout + result.stderr
    if result.returncode == 0 or expected not in diagnostic:
        raise SystemExit(f"{name}: incorrect rejection\n{diagnostic}")
    print(f"{name}: expected rejection", flush=True)
