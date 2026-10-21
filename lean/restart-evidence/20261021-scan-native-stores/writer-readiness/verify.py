import argparse,hashlib,json
from pathlib import Path
HERE=Path(__file__).resolve().parent
p=argparse.ArgumentParser();p.add_argument('--root',type=Path,required=True);p.add_argument('--live',action='store_true');args=p.parse_args()
manifest=json.loads((HERE/'manifest.json').read_text())
for item in manifest['files']:
 data=(HERE/item['path']).read_bytes()
 assert len(data)==item['bytes'] and hashlib.sha256(data).hexdigest()==item['sha256'],item['path']
pins=json.loads((HERE/'source-pins.json').read_text())
assert pins['new_lean_commands']==pins['new_lake_commands']==pins['new_canonical_commands']==0
assert not pins['official_edits']
for item in pins['sources']:
 data=(HERE/item['snapshot']).read_bytes()
 assert len(data)==item['bytes'] and hashlib.sha256(data).hexdigest()==item['sha256']
 if args.live: assert (args.root/item['path']).read_bytes()==data,item['path']
print(json.dumps({'status':'PASS','sources':len(pins['sources']),'live':args.live,'new_proof_commands':0}))
