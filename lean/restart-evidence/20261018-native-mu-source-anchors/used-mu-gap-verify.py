import hashlib,json
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
manifest=json.loads((HERE/'used-mu-gap-manifest.json').read_text())
for item in manifest['entries']:
    path=ROOT/item['path']
    assert path.is_file() and path.stat().st_size==item['bytes'],path
    assert hashlib.sha256(path.read_bytes()).hexdigest()==item['sha256'],path
assert manifest['counts']=={'public':0,'constructed':0,'executions':0}
print(json.dumps({'status':'PASS','entries':len(manifest['entries']),'public_pairs':0,'constructed_pairs':0}))
