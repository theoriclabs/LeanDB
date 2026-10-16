#!/usr/bin/env bash
set -euo pipefail
export PATH=/root/.elan/bin:$PATH
cd /work/repo/experiments/cloudflare/native
date -u
uname -a
lake build cf-native
cp .lake/build/bin/cf-native /work/out/cf-native
strip /work/out/cf-native
sha256sum /work/out/cf-native
ls -lh /work/out/cf-native
ldd /work/out/cf-native
date -u
