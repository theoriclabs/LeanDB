#!/usr/bin/env python3
"""Destroy native container in each interrupted commit window BEFORE retry."""
import argparse,json,time,uuid,urllib.request,urllib.error,pathlib,datetime
p=argparse.ArgumentParser()
p.add_argument('--url',required=True)
p.add_argument('--tokens',required=True)
p.add_argument('--evidence',required=True)
a=p.parse_args()
class NoRedirects(urllib.request.HTTPRedirectHandler):
 def redirect_request(self,req,fp,code,msg,headers,newurl): return None
urllib.request.install_opener(urllib.request.build_opener(urllib.request.ProxyHandler({}),NoRedirects()))
tokens=json.load(open(a.tokens))
out={'started':datetime.datetime.now(datetime.timezone.utc).isoformat(),'scope':'container destruction before retry in both commit windows','requests':[],'assertions':[]}
def call(path,body=None,admin=False,retry=False):
 deadline=time.monotonic()+120
 while True:
  req=urllib.request.Request(a.url+path,data=None if body is None else json.dumps(body).encode(),headers={'Authorization':'Bearer '+tokens['ADMIN_TOKEN' if admin else 'TOKEN_A'],'Content-Type':'application/json','User-Agent':'LeanDB-Cloudflare-Experiment/1.0'})
  t=time.monotonic()
  try:
   with urllib.request.urlopen(req,timeout=90) as r: status=r.status;result=json.load(r)
  except urllib.error.HTTPError as e:
   status=e.code
   try:result=json.load(e)
   except:result={'code':'non_json_http_error'}
  out['requests'].append({'path':path,'status':status,'ms':round((time.monotonic()-t)*1000,2),'response':result})
  if retry and status==503 and time.monotonic()<deadline:time.sleep(2);continue
  return status,result
def check(name,condition):
 out['assertions'].append({'name':name,'passed':bool(condition)})
 if not condition:raise AssertionError(name)
key='crash-'+uuid.uuid4().hex
try:
 s,initial=call('/durable/snapshot',{'tenant':'alpha'},retry=True);check('initial snapshot',s==200 and initial.get('ok') is True)
 s,res=call('/durable/command',{'requestId':key+'-create','command':{'type':'create','tenant':'alpha','key':key,'value':0}},retry=True);check('seed',s==200 and res.get('ok') is True)
 expected=0
 for point,delta in [('after-journal',7),('after-native',5)]:
  s,before=call('/durable/status',retry=True);check(point+' status before',s==200)
  s,res=call('/durable/admin/inject',{'point':point},admin=True);check(point+' armed',s==200 and res.get('ok') is True)
  body={'requestId':key+'-'+point,'command':{'type':'increment','tenant':'alpha','key':key,'delta':delta}}
  s,res=call('/durable/command',body);check(point+' interrupted',s==503 and res.get('code')=='injected_'+point.replace('-','_'))
  s,res=call('/durable/admin/destroy',{},admin=True);check(point+' destroyed before retry',s==200 and res.get('ok') is True)
  s,res=call('/durable/command',body,retry=True)
  expected+=delta
  check(point+' recovered exactly once',s==200 and res.get('ok') is True and res.get('value')==expected)
  s,again=call('/durable/command',body,retry=True);check(point+' stable receipt',s==200 and again==res)
  s,after=call('/durable/status',retry=True);check(point+' new container boot',s==200 and before['bootId']!=after['bootId'])
  s,snapshot=call('/durable/snapshot',{'tenant':'alpha'},retry=True)
  check(point+' exact recovered state',s==200 and snapshot.get('sum')==initial['sum']+expected and next((i['value'] for i in snapshot['items'] if i['key']==key),None)==expected)
 out['outcome']='passed'
except Exception as e:
 out['outcome']='failed';out['error']=type(e).__name__+': '+str(e)
finally:
 out['finished']=datetime.datetime.now(datetime.timezone.utc).isoformat()
 text=json.dumps(out,indent=2)
 for v in tokens.values():text=text.replace(v,'[REDACTED]')
 pathlib.Path(a.evidence).write_text(text+'\n')
 print(json.dumps({'outcome':out['outcome'],'assertions':len(out['assertions']),'requests':len(out['requests']),'evidence':a.evidence}))
raise SystemExit(0 if out['outcome']=='passed' else 1)
