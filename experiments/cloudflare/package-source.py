#!/usr/bin/env python3
"""Package pinned source and fixture; include no credentials or build caches."""
import argparse,io,pathlib,subprocess,tarfile,tempfile,shutil
p=argparse.ArgumentParser()
p.add_argument("output")
p.add_argument("--ontology",default="/Users/harshwork/code/leanontology")
a=p.parse_args()
experiment=pathlib.Path(__file__).resolve().parent
repo=experiment.parents[1]
with tempfile.TemporaryDirectory(prefix="leandb-cf-source-") as tmp:
 root=pathlib.Path(tmp)/"LeanDB";root.mkdir()
 for source,revision,dest in [(repo,"8920c70",root),(pathlib.Path(a.ontology),"322a4c12631dd8ece6ae9841a5e6b630d08d1e3b",root/"vendor/leanontology")]:
  dest.mkdir(parents=True,exist_ok=True)
  blob=subprocess.check_output(["git","-C",str(source),"archive",revision])
  with tarfile.open(fileobj=io.BytesIO(blob)) as t:
   for m in t.getmembers():
    if m.name.startswith("/") or ".." in pathlib.PurePosixPath(m.name).parts: raise RuntimeError("unsafe archive path")
   t.extractall(dest)
 fixture=root/"experiments/cloudflare/native";fixture.mkdir(parents=True)
 for name in ["CfNative.lean","Main.lean","lakefile.toml","lean-toolchain"]:
  shutil.copy2(experiment/"native"/name,fixture/name)
 shutil.copy2(experiment/"build-cloud.sh",root/"experiments/cloudflare/build-cloud.sh")
 lake=root/"lakefile.toml"
 lake.write_text(lake.read_text().replace('git = "https://github.com/theoriclabs/leanontology"\nrev = "322a4c12631dd8ece6ae9841a5e6b630d08d1e3b"','path = "vendor/leanontology"'))
 (root/"lake-manifest.json").unlink()
 with tarfile.open(a.output,"w:gz") as t:t.add(root,arcname="LeanDB")
 print(f"Created {a.output}: {pathlib.Path(a.output).stat().st_size} bytes; pinned source only")
