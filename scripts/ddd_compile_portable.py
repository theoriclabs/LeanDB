#!/usr/bin/env python3
"""Compile peer portable sources serially into this repo, without mutating peer builds.
Developer-only checkout location is supplied by CLI, never by a release manifest.
"""
import argparse
import os
from pathlib import Path
import re
import subprocess

p = argparse.ArgumentParser()
p.add_argument('source', type=Path, help='LeanReact engine directory')
p.add_argument('output', type=Path)
p.add_argument('modules', nargs='+')
p.add_argument('--lean', default='lean')
p.add_argument('--search-path', default='', help='Already-built dependencies for this toolchain')
a = p.parse_args()
a.output.mkdir(parents=True, exist_ok=True)
a.source = a.source.resolve()
a.output = a.output.resolve()
seen = set()
env = dict(os.environ, LEAN_PATH=os.pathsep.join(filter(None, [str(a.output), a.search_path])), LEAN_NUM_THREADS='2')

def build(module):
    if module in seen:
        return
    src = a.source / (module.replace('.', '/') + '.lean')
    if not src.exists():
        return  # Toolchain-provided import.
    source = src.read_text()
    for line in source.splitlines():
        match = re.match(r'^\s*(?:public\s+)?import\s+(.+?)\s*$', line)
        if match:
            for dep in match[1].split():
                build(dep)
    out = a.output / (module.replace('.', '/') + '.olean')
    out.parent.mkdir(parents=True, exist_ok=True)
    print(module, flush=True)
    subprocess.run([a.lean, '-j', '2', '-R', str(a.source), '-o', str(out), str(src)],
                   env=env, check=True)
    seen.add(module)

for module in a.modules:
    build(module)
