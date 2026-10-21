import argparse,hashlib,json
from pathlib import Path
HERE=Path(__file__).resolve().parent
def check(base,entry):
 data=(base/entry['path']).read_bytes()
 assert len(data)==entry['bytes'] and hashlib.sha256(data).hexdigest()==entry['sha256'],entry['path']
p=argparse.ArgumentParser();p.add_argument('--root',type=Path,default=Path('/home/tritlo/Code/mcfta'));p.add_argument('--live',action='store_true');a=p.parse_args()
m=json.loads((HERE/'manifest.json').read_text())
for e in m['files']:check(HERE,e)
for e in m['sources']:
 check(HERE/'inputs/root',e)
 if a.live:check(a.root,e)
assert json.loads((HERE/'source-pins.json').read_text())['files']==m['sources']
s=json.loads((HERE/'selection.json').read_text());assert s['finalized'] and s['lean_jobs']==s['new_public_pairs']==s['constructed_pairs']==0
assert s['target_public_heads']==['fold','pass','indexed_phase']
assert s['class_dependency_sha256']==m['sources'][0]['sha256']
print(json.dumps({'status':'PASS','pins':len(m['files'])+len(m['sources']),'lean_jobs':0,'new_public_pairs':0,'live':a.live}))
