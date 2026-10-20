#!/usr/bin/env python3
"""Verify immutable private-core evidence without running Lean."""
import argparse,hashlib,json
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--root',type=Path,required=True);p.add_argument('--live',action='store_true');a=p.parse_args();h=Path(__file__).resolve().parent
j=lambda name:json.loads((h/name).read_text())
def check(base,item):
 raw=(base/item['path']).read_bytes()
 assert len(raw)==item['bytes'] and hashlib.sha256(raw).hexdigest()==item['sha256'],item['path']
m=j('generated-backedge-manifest.json')
for item in m['files']:check(h,item)
pins=j('generated-backedge-source-pins.json')['files']
for item in pins:
 check(h/'inputs',item)
 if a.live:check(a.root,item)
s=j('generated-backedge-selection.json');assert (s['owned_lean_jobs'],s['failed_lean_jobs'],s['owned_official_public_pairs'],s['owned_constructed_pairs'],s['owned_full_public_jobs'])==(3,1,0,0,0)
for attempt in s['attempts']:
 stem=attempt['stem'];r=j(stem+'.json');assert r['exit_code']==attempt['exit_code']
 assert hashlib.sha256((h/r['source']).read_bytes()).hexdigest()==r['sha256']
 assert '-Dlinter.all=true' in r['command'] and r['command'][0].endswith('lean4---v4.34.1/bin/lean')
 assert r['wrapper'][1:5]==['--mem','4G','--time','5m']
 assert j(stem+'.limits.json')=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
 usage=j(stem+'.usage.json');assert usage['age_seconds']<120 and usage['remaining_percent']>1
r=j(s['selected_strict']+'.json');assert (h/r['log']).read_bytes()==b''
assert (h/r['source']).read_bytes()==(h/s['source']).read_bytes()
text=(h/s['source']).read_text();assert text.count('private theorem ')==2
assert '.resident entry rfl' in text and 'entry.key ≠ targetKey' in text
assert 'origins selectedRow selectedInside' in text
assert 'SourceCurrentSourceCaptureOriginalSlots.original_slot' in text
print(json.dumps(dict(status='PASS',mode='live' if a.live else 'portable',root_pins=len(pins),local_pins=len(m['files']),owned_lean_jobs=3,failed_lean_jobs=1,owned_official_public_pairs=0,owned_constructed_pairs=0,selected_log_bytes=0),indent=2))
