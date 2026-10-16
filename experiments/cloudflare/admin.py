#!/usr/bin/env python3
"""Temporary experiment operator. Tokens are read from a private file, never printed."""
import argparse,json,sys,urllib.request,urllib.error
BASE="https://leandb-cf-exp-20261009.harsh-420.workers.dev"
p=argparse.ArgumentParser()
p.add_argument("action",choices=["exec","call","workspace","publish","destroy"])
p.add_argument("--mode",default="durable",choices=["durable","ephemeral"])
p.add_argument("--file")
p.add_argument("--command")
p.add_argument("--output")
p.add_argument("--tokens",default="/private/tmp/leandb-cf-20261009/secrets.json")
a=p.parse_args()
s=json.load(open(a.tokens))
if a.action=="workspace":
    data=open(a.file,"rb").read(); kind="application/gzip"
elif a.action=="exec":
    data=json.dumps({"command":a.command or sys.stdin.read(),"options":{"cwd":"/work","timeout":30}}).encode();kind="application/json"
elif a.action=="call":
    data=open(a.file,"rb").read() if a.file else sys.stdin.buffer.read();kind="application/json"
else:
    data=b"{}";kind="application/json"
req=urllib.request.Request(f"{BASE}/{a.mode}/admin/{a.action}",data=data,headers={"Authorization":"Bearer "+s["ADMIN_TOKEN"],"Content-Type":kind,"User-Agent":"LeanDB-Cloudflare-Experiment/1.0"})
try:
    with urllib.request.urlopen(req,timeout=120) as r: result=r.read()
except urllib.error.HTTPError as e:
    result=e.read()
    print("HTTP "+str(e.code),file=sys.stderr)
    for v in s.values(): result=result.replace(v.encode(),b"[REDACTED]")
    sys.stdout.buffer.write(result)
    raise SystemExit(1)
for v in s.values(): result=result.replace(v.encode(),b"[REDACTED]")
if a.output: open(a.output,"wb").write(result)
sys.stdout.buffer.write(result)
