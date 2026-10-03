#!/usr/bin/env python3
"""Require each negative Lean fixture to fail for its intended type error."""
import os
from pathlib import Path
import subprocess

root = Path(__file__).resolve().parent.parent
subprocess.run(["lake", "build", "TestsDdd"], cwd=root,
               env=dict(os.environ, LEAN_NUM_THREADS="2"), check=True,
               stdout=subprocess.DEVNULL)
fixtures = {
    "EmptyCorrespondence": "3 explicit field",
    "WrongParent": "Id Party",
    "ForgedHandle": "MemberHandle.mk",
    "EscapedHandle": "Unit",
    # Milestone 2: entity-based RSVP, proof-carrying reads, typed migrations.
    "MissingConflict": "Missing cases:\n(Except.error Rsvp.Unique.onePerGuest)",
    "SwappedLink": "toCol (Entity.get Rsvp.Field.guest",
    "UnprovenGuests": "CanSeeGuests row.val.guestList role = true → Read S (List String)",
    "WrongFill": "Entity.fieldTy Party.Field.guestList",
    "UnknownFillField": "has no stored field 'guestlist'",
}
for name, expected in fixtures.items():
    result = subprocess.run(
        ["lake", "env", "lean", "-j", "2", f"fixtures/ddd/{name}.lean"],
        cwd=root, env=dict(os.environ, LEAN_NUM_THREADS="2"),
        text=True, capture_output=True, check=False,
    )
    if result.returncode == 0 or expected not in result.stdout + result.stderr:
        raise SystemExit(f"{name}: incorrect rejection\n{result.stdout}{result.stderr}")
    print(f"{name}: expected rejection")

# Positive cross-module regression: persistent relation metadata and actual
# stored FK actions must agree when assembly lives in a different module.
output = root / ".lake/ddd-fixtures/Imported/Declaration.olean"
output.parent.mkdir(parents=True, exist_ok=True)
env = dict(os.environ, LEAN_NUM_THREADS="2", LEAN_PATH=str(output.parent.parent))
subprocess.run(["lake", "env", "lean", "-j", "2", "-R", "fixtures/ddd",
                "-o", str(output), "fixtures/ddd/Imported/Declaration.lean"], cwd=root, env=env, check=True)
subprocess.run(["lake", "env", "lean", "-j", "2", "-R", "fixtures/ddd",
                "--load-dynlib", ".lake/packages/leansqlite/.lake/build/lib/libleansqlite.dylib",
                "--load-dynlib", ".lake/packages/leansqlite/.lake/build/lib/libleansqlite_SQLite.dylib",
                "--run", "fixtures/ddd/Imported/Schema.lean"], cwd=root, env=env, check=True)
