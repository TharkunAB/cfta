import hashlib
import json
import shutil
import subprocess
from pathlib import Path

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
target=HERE/'writer-readiness'
assert not target.exists()
shutil.copytree('/tmp/mcfta-parent-writer-ready-addendum',target)
verifier='''import argparse,hashlib,json
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
'''
(target/'verify.py').write_text(verifier)
files=[]
for path in sorted(target.rglob('*')):
 if path.is_file():
  data=path.read_bytes();files.append({'path':str(path.relative_to(target)),'bytes':len(data),'sha256':hashlib.sha256(data).hexdigest()})
(target/'manifest.json').write_text(json.dumps({'files':files},indent=2)+'\n')
for mode in [[],['--live']]:
 subprocess.run(['/usr/bin/python3',str(target/'verify.py'),'--root',str(ROOT),*mode],cwd='/',check=True)
registry=HERE/'components.json'
items=json.loads(registry.read_text());items.append({'path':'writer-readiness','verifier':'verify.py','extra':['--root',str(ROOT)],'live':True})
registry.write_text(json.dumps(items,indent=2)+'\n')
print(json.dumps({'status':'PASS','files':len(files)}))
