#!/usr/bin/env python3
from pathlib import Path
import argparse,hashlib,json,subprocess,sys
p=argparse.ArgumentParser();p.add_argument('--root',type=Path,required=True);p.add_argument('--live',action='store_true');a=p.parse_args();h=Path(__file__).resolve().parent
read=lambda p:json.loads(p.read_text())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def check(p,pin):
 assert p.is_file() and p.stat().st_size==pin['bytes'] and sha(p)==pin['sha256'],str(p)
m=read(h/'review-manifest.json');assert m['finalized']
for x in m['files']:check(h/x['path'],x)
sources=read(h/'review-source-pins.json')['sources'];assert sources==m['sources']
for x in sources:
 q=h/x['snapshot'];check(q,x);lines=q.read_bytes().splitlines(keepends=True)
 for span in x['reviewed_ranges']:assert hashlib.sha256(b''.join(lines[span['start']-1:span['end']])).hexdigest()==span['sha256']
 if a.live:check(a.root/x['path'],x)
s=read(h/'review-owner-selection.json');assert sha(h/'owner'/s['owner_manifest'])==s['owner_manifest_sha256']
assert s['owner_frozen'] and s['owner_proof_jobs']==s['reviewer_proof_jobs']==s['reviewer_runtime_jobs']==s['reviewer_official_edits']==0
cmd=[sys.executable,str(h/'owner'/s['owner_verifier']),'--root',str(a.root)]
if a.live:cmd.append('--live')
owner=subprocess.run(cmd,cwd='/',capture_output=True,text=True,check=True);assert json.loads(owner.stdout)['status']=='PASS';assert read(h/'clearance.json')['judgment']=='clear'
print(json.dumps({'status':'PASS','live':a.live,'local_pins':len(m['files']),'root_pins':len(sources),'reviewed_ranges':sum(len(x['reviewed_ranges'])for x in sources),'owner_verifier':'PASS','reviewer_proof_jobs':0,'reviewer_runtime_jobs':0,'manifest_sha256':sha(h/'review-manifest.json')},indent=2))
