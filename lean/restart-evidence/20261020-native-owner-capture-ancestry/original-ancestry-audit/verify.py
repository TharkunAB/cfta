import argparse,hashlib,json
from pathlib import Path
h=Path(__file__).resolve().parent
p=argparse.ArgumentParser();p.add_argument('--root',type=Path,default=Path('/home/tritlo/Code/mcfta'));a=p.parse_args()
m=json.loads((h/'manifest.json').read_text())
for base,items in [(h,m['files']),(a.root,m['sources'])]:
 for e in items:
  d=(base/e['path']).read_bytes();assert len(d)==e['bytes'] and hashlib.sha256(d).hexdigest()==e['sha256'],e['path']
print(json.dumps({'status':'PASS','pins':len(m['files'])+len(m['sources']),'lean_jobs':0,'proof_pairs':0}))
