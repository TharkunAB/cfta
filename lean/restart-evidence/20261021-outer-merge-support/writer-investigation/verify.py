import argparse,hashlib,json
from pathlib import Path
HERE=Path(__file__).resolve().parent
p=argparse.ArgumentParser();p.add_argument('--root',type=Path,default=Path('/home/tritlo/Code/mcfta'));p.add_argument('--live',action='store_true');a=p.parse_args()
m=json.loads((HERE/'manifest.json').read_text())
for group,base in [('files',HERE),('sources',HERE/'inputs/root')]:
 for e in m[group]:
  data=(base/e['path']).read_bytes();assert len(data)==e['bytes'] and hashlib.sha256(data).hexdigest()==e['sha256'],e['path']
  if group=='sources' and a.live:
   data=(a.root/e['path']).read_bytes();assert len(data)==e['bytes'] and hashlib.sha256(data).hexdigest()==e['sha256'],e['path']
print(json.dumps(dict(status='PASS',pins=len(m['files'])+len(m['sources']),lean_jobs=0,live=a.live)))
