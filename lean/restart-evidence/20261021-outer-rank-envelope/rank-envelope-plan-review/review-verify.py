#!/usr/bin/env python3
from pathlib import Path
import argparse,hashlib,json,subprocess,sys
p=argparse.ArgumentParser();p.add_argument('--root',type=Path,required=True);p.add_argument('--live',action='store_true');p.add_argument('--toolchain-source',type=Path);a=p.parse_args();h=Path(__file__).resolve().parent
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
assert sha(h/'owner'/'selection.json')==s['owner_selection_sha256']
assert s['selected_public_heads']==['envelope','retains'] and s['deferred_public_heads']==['stage_bounds']
assert not s['envelope_defined'] and not s['retention_proved'] and not s['stage_bounds_proved'] and not s['adequacy_proved']
assert not s['implementation_authorized'] and s['hard_total_source_line_stop']==250
assert s['owner_frozen'] and s['owner_proof_jobs']==s['reviewer_proof_jobs']==s['reviewer_runtime_jobs']==s['reviewer_official_edits']==0
cmd=[sys.executable,str(h/'owner'/s['owner_verifier']),'--root',str(a.root)]
if a.live:cmd.append('--live')
if a.toolchain_source:cmd+=['--toolchain-source',str(a.toolchain_source)]
owner=subprocess.run(cmd,cwd='/',capture_output=True,text=True,check=True);out=json.loads(owner.stdout);assert out['status']=='PASS' and out['live']==a.live and out['toolchain_pins']==4 and out['source_ranges']==19;assert read(h/'clearance.json')['judgment']=='clear'
print(json.dumps({'status':'PASS','live':a.live,'local_pins':len(m['files']),'root_pins':len(sources),'root_reviewed_ranges':sum(len(x['reviewed_ranges'])for x in sources),'toolchain_pins':4,'toolchain_reviewed_ranges':8,'owner_index_sources':10,'owner_index_ranges':19,'owner_verifier':'PASS','reviewer_proof_jobs':0,'reviewer_runtime_jobs':0,'reviewer_official_edits':0,'envelope_defined':False,'retention_proved':False,'stage_bounds_proved':False,'adequacy_proved':False,'manifest_sha256':sha(h/'review-manifest.json')},indent=2))
