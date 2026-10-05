#!/usr/bin/env python3
"""Validate the optional bridge against a supplied portable checkout.

No release manifest receives local paths; peer sources are compiled read-only
into this repository's ignored build output, with bounded compiler concurrency.
"""
import argparse
import os
from pathlib import Path
import subprocess
import shutil
import re

parser = argparse.ArgumentParser()
parser.add_argument("portable", type=Path, help="LeanReact repository")
parser.add_argument("--spec", type=Path, help="Shared specification repository; test its unchanged Partiful.Domain")
args = parser.parse_args()
root = Path(__file__).resolve().parent.parent
env = dict(os.environ, LEAN_NUM_THREADS="2")

def run(command, current_env=env):
    subprocess.run(command, cwd=root, env=current_env, check=True)

run(["lake", "build", "LeanDb", "CheckAxioms"])
run(["python3", "scripts/ddd_compile_portable.py", str(args.portable.resolve() / "engine"),
     ".lake/ddd-portable", "LeanApp.Domain"])
env["LEAN_PATH"] = os.pathsep.join(str(root / path) for path in [".lake/ddd-portable", ".lake/ddd-domain", ".lake/ddd-post/lib"])
for module in ["LeanDbDomain.Storage", "LeanDbDomain.Witness", "LeanDbDomain.Resources", "LeanDbDomain.Access", "LeanDbDomain.Schema", "LeanDbDomain.Operations", "LeanDbDomain"]:
    stem = module.replace(".", "/")
    out = root / ".lake/ddd-domain" / (stem + ".olean")
    out.parent.mkdir(parents=True, exist_ok=True)
    run(["lake", "env", "lean", "-j", "2", "-R", "adapters/domain", "-o", str(out),
         "adapters/domain/" + stem + ".lean"])
def run_fixture(name):
    run(["lake", "env", "lean", "-j", "2", "--load-dynlib",
         str(root / ".lake/packages/leansqlite/.lake/build/lib/libleansqlite.dylib"),
         "--load-dynlib", str(root / ".lake/packages/leansqlite/.lake/build/lib/libleansqlite_SQLite.dylib"),
         "-R", "adapters/domain", "--run", f"adapters/domain/Tests/{name}.lean"])

run_fixture("Access")
run_fixture("UniqueSources")
negative = subprocess.run(
    ["lake", "env", "lean", "-j", "2", "-R", "adapters/domain", "adapters/domain/Tests/UniqueEvolution.lean"],
    cwd=root, env=env, text=True, capture_output=True, check=False)
diagnostic = negative.stdout + negative.stderr
if negative.returncode == 0 or "Missing cases" not in diagnostic or "byEmail" not in diagnostic:
    raise SystemExit("Portable uniqueness evolution: incorrect rejection\n" + diagnostic)
print("Portable uniqueness evolution: expected byEmail exhaustiveness rejection")
negative = subprocess.run(
    ["lake", "env", "lean", "-j", "2", "-R", "adapters/domain", "adapters/domain/Tests/WrongProjection.lean"],
    cwd=root, env=env, text=True, capture_output=True, check=False)
diagnostic = negative.stdout + negative.stderr
if negative.returncode == 0 or "rfl" not in diagnostic or "Email" not in diagnostic or "Name" not in diagnostic:
    raise SystemExit("Typed field projection: incorrect rejection\n" + diagnostic)
print("Typed field projection: expected Email-to-Name equality rejection")
negative = subprocess.run(
    ["lake", "env", "lean", "-j", "2", "-R", "adapters/domain", "adapters/domain/Tests/WrongUniqueGetter.lean"],
    cwd=root, env=env, text=True, capture_output=True, check=False)
diagnostic = negative.stdout + negative.stderr
if negative.returncode == 0 or "rfl" not in diagnostic or "Profile.byEmail.field.get" not in diagnostic or "email" not in diagnostic:
    raise SystemExit("Unique descriptor getter: incorrect rejection\n" + diagnostic)
print("Unique descriptor getter: expected swapped-getter equality rejection")
run_fixture("Storage")
run_fixture("ProjectionEvolution")
# Milestone 2 on original portable records: migration gate, typed backfill,
# semi-join projection and ordinary-entity cascade.
run_fixture("GateEvolution")
# Generality fixture: an unrelated library-loans domain from public API only.
run_fixture("LibraryRuntime")
# Structured values (lists, records) stored as one canonical-JSON column.
run_fixture("JsonColumnRuntime")
# A `represent`ed private-constructor type as a field (needs LeanReact's `represent`).
if (args.portable.resolve() / "engine/LeanApp/Domain/Represent.lean").exists():
    run_fixture("RepresentRuntime")
for fixture, expected, error_count in [
    ("MissingProjection", ("failed to synthesize", "HasProjectionResource", "alias"), 1),
    ("WrongProjectionTarget", ("type mismatch", "FieldStorage", "relation.target.entity", "HasProjectionResource"), 2),
    ("WrongProjectionGetter", ("rfl", "swapped"), 1),
    ("WrongProjectionLens", ("failed to synthesize", "HasProjectionResource", "name"), 1),
]:
    rejection = subprocess.run(
        ["lake", "env", "lean", "-j", "2", "-R", "adapters/domain", f"adapters/domain/Tests/{fixture}.lean"],
        cwd=root, env=env, text=True, capture_output=True, check=False)
    diagnostic = rejection.stdout + rejection.stderr
    if (rejection.returncode == 0 or
            len(re.findall(r"\berror(?:\([^\n]*?\))?:", diagnostic)) != error_count or
            any(part.lower() not in diagnostic.lower() for part in expected)):
        raise SystemExit(f"{fixture}: incorrect compiler rejection\n" + diagnostic)
    print(f"{fixture}: expected typed projection rejection", flush=True)
# Milestone 2 wave 2: the post's domain from the portable checkout, imported
# unchanged, runs natively through shared Flow.run on SQLite.
post = args.portable.resolve() / "tests/domain/PostPart1.lean"
if post.exists():
    post_source = root / ".lake/ddd-post/src/PostPart1.lean"
    post_library = root / ".lake/ddd-post/lib"
    post_source.parent.mkdir(parents=True, exist_ok=True)
    post_library.mkdir(parents=True, exist_ok=True)
    (root / ".lake/ddd-m2-scratch").mkdir(parents=True, exist_ok=True)
    shutil.copyfile(post, post_source)
    run(["lake", "env", "lean", "-j", "2", "-R", str(post_source.parent), "-o",
         str(post_library / "PostPart1.olean"), str(post_source)])
    run_fixture("PostRuntime")
    rejection = subprocess.run(
        ["lake", "env", "lean", "-j", "2", "-R", "adapters/domain", "adapters/domain/Tests/UndeclaredUniqueKey.lean"],
        cwd=root, env=env, text=True, capture_output=True, check=False)
    diagnostic = rejection.stdout + rejection.stderr
    if (rejection.returncode == 0 or
            len(re.findall(r"\berror(?:\([^\n]*?\))?:", diagnostic)) != 1 or
            any(part not in diagnostic for part in ("HasUniqueResource", "forgedKey"))):
        raise SystemExit("UndeclaredUniqueKey: incorrect compiler rejection\n" + diagnostic)
    print("UndeclaredUniqueKey: expected rejection (no evidence for an undeclared key)", flush=True)
if args.spec:
    source = root / ".lake/ddd-partiful/src/Partiful/Domain.lean"
    library = root / ".lake/ddd-partiful/lib"
    source.parent.mkdir(parents=True, exist_ok=True)
    (library / "Partiful").mkdir(parents=True, exist_ok=True)
    shutil.copyfile(args.spec.resolve() / "partiful/Domain.lean", source)
    env["LEAN_PATH"] += os.pathsep + str(library)
    run(["lake", "env", "lean", "-j", "2", "-R", str(source.parents[1]), "-o",
         str(library / "Partiful/Domain.olean"), str(source)])
    run_fixture("PartifulProjection")
