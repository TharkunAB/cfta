from pathlib import Path
import argparse,hashlib,json
p=argparse.ArgumentParser();p.add_argument('--root',type=Path,default=Path('/home/tritlo/Code/mcfta'));a=p.parse_args()
here=Path(__file__).resolve().parent
m=json.loads((here/'next-owner-manifest.json').read_text())
for base,entries in [(here,m['files']),(a.root,m['sources'])]:
 for i in entries:
  b=(base/i['path']).read_bytes()
  assert len(b)==i['bytes'] and hashlib.sha256(b).hexdigest()==i['sha256'],i['path']
print(json.dumps({'status':'PASS','pins':len(m['files'])+len(m['sources']),'new_lean_jobs':0,'new_proof_pairs':0,'scope':'design only; proposed owner endpoint remains unproved'}))
