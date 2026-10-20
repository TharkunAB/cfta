#!/usr/bin/env python3
import argparse,hashlib,json
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--root',type=Path,required=True);p.add_argument('--live',action='store_true');a=p.parse_args();h=Path(__file__).resolve().parent
j=lambda n:json.loads((h/n).read_text())
def check(base,item):
 raw=(base/item['path']).read_bytes();assert len(raw)==item['bytes'] and hashlib.sha256(raw).hexdigest()==item['sha256'],item['path']
m=j('plan-manifest.json')
for item in m['files']:check(h,item)
for item in j('plan-source-pins.json')['files']:
 check(h/'inputs',item)
 if a.live:check(a.root,item)
assert (m['owned_lean_jobs'],m['owned_public_pairs'],m['owned_constructed_pairs'])==(0,0,0)
text=(h/'plan.md').read_text();assert 'Design only.' in text and 'proposed theorem is unproved' in text
print(json.dumps(dict(status='PASS',mode='live' if a.live else 'portable',root_pins=len(j('plan-source-pins.json')['files']),local_pins=len(m['files']),owned_lean_jobs=0,owned_public_pairs=0,owned_constructed_pairs=0),indent=2))
