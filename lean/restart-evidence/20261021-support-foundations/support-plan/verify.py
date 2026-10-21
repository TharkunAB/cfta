import argparse,hashlib,json
from pathlib import Path
p=Path(__file__).resolve().parent
args=argparse.ArgumentParser()
args.add_argument('--root',type=Path,default=Path('/home/tritlo/Code/mcfta'))
args.add_argument('--live',action='store_true')
a=args.parse_args()
m=json.loads((p/'manifest.json').read_text())
for e in m['files']:
 b=(p/e['path']).read_bytes();assert len(b)==e['bytes'] and hashlib.sha256(b).hexdigest()==e['sha256'],e['path']
for e in m['sources']:
 b=(p/'inputs/root'/e['path']).read_bytes();assert len(b)==e['bytes'] and hashlib.sha256(b).hexdigest()==e['sha256'],e['path']
 if a.live:
  assert (a.root/e['path']).read_bytes()==b,e['path']
assert json.loads((p/'source-pins.json').read_text())['files']==m['sources']
print(json.dumps({'status':'PASS','pins':len(m['files'])+len(m['sources']),'lean_jobs':0,'proposed_signature_theorem':True,'live':a.live}))
