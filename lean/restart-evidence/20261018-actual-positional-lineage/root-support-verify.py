import hashlib, json
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
manifest=json.loads((HERE/'root-support-manifest.json').read_text())
for item in manifest['entries']:
    path=ROOT/item['path']
    assert path.stat().st_size==item['bytes'], path
    assert hashlib.sha256(path.read_bytes()).hexdigest()==item['sha256'], path
assert manifest['executions']==[]
print(json.dumps({'status':'PASS','entries':len(manifest['entries']),'executions':0}))
