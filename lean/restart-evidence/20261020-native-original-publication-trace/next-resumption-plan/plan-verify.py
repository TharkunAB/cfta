#!/usr/bin/env python3
import argparse,hashlib,json
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--root',type=Path,required=True);p.add_argument('--live',action='store_true');a=p.parse_args();h=Path(__file__).resolve().parent
j=lambda n:json.loads((h/n).read_text())
def check(base,item):
 b=(base/item['path']).read_bytes();assert len(b)==item['bytes'] and hashlib.sha256(b).hexdigest()==item['sha256'],item['path']
m=j('plan-manifest.json')
for item in m['files']:check(h,item)
s=j('plan-source-pins.json')
for item in s['files']:
 check(h/'inputs',item)
 if a.live:check(a.root,item)
check(h,s['candidate']);official=a.root/s['candidate']['official_path'];checked=False
if a.live and official.exists():
 b=official.read_bytes();assert len(b)==s['candidate']['bytes'] and hashlib.sha256(b).hexdigest()==s['candidate']['sha256'];checked=True
text=(h/'plan.md').read_text();assert 'Design only.' in text and 'zero Lean runs and zero proof pairs' in text
assert m['owned_lean_runs']==0 and m['owned_public_pairs']==0 and m['owned_constructed_pairs']==0
print(json.dumps(dict(result='PASS',mode='live' if a.live else 'portable',root_pins=len(s['files']),candidate_pins=1,local_pins=len(m['files']),official_trace_live_checked=checked,owned_lean_runs=0,owned_public_pairs=0,owned_constructed_pairs=0),indent=2))
