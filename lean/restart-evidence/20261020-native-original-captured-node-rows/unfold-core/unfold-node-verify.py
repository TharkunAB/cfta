#!/usr/bin/env python3
import argparse,hashlib,json
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--root',type=Path,required=True);p.add_argument('--live',action='store_true');a=p.parse_args();h=Path(__file__).resolve().parent
j=lambda n:json.loads((h/n).read_text())
def check(base,item):
 b=(base/item['path']).read_bytes();assert len(b)==item['bytes'] and hashlib.sha256(b).hexdigest()==item['sha256'],item['path']
m=j('unfold-node-manifest.json')
for item in m['files']:check(h,item)
for item in j('unfold-node-source-pins.json')['files']:
 check(h/'inputs',item)
 if a.live:check(a.root,item)
s=j('unfold-node-selection.json');assert (s['actual_lean_jobs'],s['retained_failures'],s['official_public_pairs'],s['constructed_pairs'],s['canonical_runs'],s['auxiliary_full_runs'])==(1,0,0,0,0,0)
r=j(s['selected_strict']+'.json');assert r['exit_code']==0;assert 'leanprover--lean4---v4.34.1/bin/lean' in r['command'][0];assert r['wrapper'][1:5]==['--mem','4G','--time','5m'];assert j(r['limits'])=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
b=(h/r['source']).read_bytes();assert hashlib.sha256(b).hexdigest()==r['sha256']==s['source_sha256'];assert b==(h/'SourceCurrentNativeCapturedUnfoldNodeCore.lean').read_bytes();assert (h/r['log']).read_bytes()==b''
u=j(s['selected_strict']+'.usage.json');assert u['age_seconds']<120 and u['remaining_percent']>1
snippet=(h/'captured-unfold-node-snippet.lean.txt').read_bytes();assert hashlib.sha256(snippet).hexdigest()==s['snippet_sha256'];assert snippet.decode().strip() in b.decode();assert snippet.decode().startswith('private theorem captured_unfold_nodes');assert 'sorry' not in snippet.decode() and 'axiom' not in snippet.decode()
assert len((h/'unfold-node-peaks-final.txt').read_text().splitlines())==1
print(json.dumps(dict(status='PASS',mode='live' if a.live else 'portable',root_pins=len(j('unfold-node-source-pins.json')['files']),local_pins=len(m['files']),actual_lean_jobs=1,retained_failures=0,official_public_pairs=0,constructed_pairs=0,auxiliary_full_runs=0),indent=2))
