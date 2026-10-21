import argparse,hashlib,json
from pathlib import Path
HERE=Path(__file__).resolve().parent
ap=argparse.ArgumentParser()
ap.add_argument('--root',type=Path,default=Path('/home/tritlo/Code/mcfta'))
ap.add_argument('--live',action='store_true')
a=ap.parse_args()
m=json.loads((HERE/'manifest.json').read_text())
for i in m['files']:
    b=(HERE/i['path']).read_bytes()
    assert len(b)==i['bytes'] and hashlib.sha256(b).hexdigest()==i['sha256'],i['path']
pins=json.loads((HERE/'source-pins.json').read_text())
for i in pins['sources']:
    b=(HERE/i['snapshot']).read_bytes()
    assert len(b)==i['bytes'] and hashlib.sha256(b).hexdigest()==i['sha256'],i['snapshot']
    if a.live:
        assert (a.root/i['path']).read_bytes()==b,i['path']
assert pins['owned_lean_lake_commands']==pins['owned_public_pairs']==0
print(json.dumps({'status':'PASS','live':a.live,'sources':len(pins['sources']),'pins':len(m['files'])+len(pins['sources']),'owned_lean_lake_commands':0,'owned_public_pairs':0,'new_theorem_proved':False}))
