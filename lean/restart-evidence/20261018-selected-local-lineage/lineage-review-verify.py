import hashlib,json
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
m=json.loads((HERE/'lineage-review-manifest.json').read_text())
for e in m['entries']:
 p=ROOT/e['path'];assert p.stat().st_size==e['bytes'];assert hashlib.sha256(p.read_bytes()).hexdigest()==e['sha256']
assert m['executions']==[]
print(json.dumps({'status':'PASS','entries':len(m['entries']),'executions':0}))
