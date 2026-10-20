import hashlib,json
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
items=json.loads((HERE/'math-review-source-pins.json').read_text())['files']
original=json.loads((HERE/'math-review-original-source-pins.json').read_text())['files']
assert len(items)==len(original)==21
for item,old in zip(items,original):
 data=(ROOT/item['path']).read_bytes()
 assert hashlib.sha256(data).hexdigest()==item['sha256']==old['sha256']
 assert len(data)==item['bytes']==old['bytes']
print(json.dumps({'status':'PASS','source_pins':len(items),'new_lean_runs':0,'new_proof_pairs':0,'author_reread_not_independent_author_review':True}))
