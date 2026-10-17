import hashlib,json,runpy
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
manifest=json.loads((HERE/'class-selected-manifest.json').read_text())
for entry in manifest['entries']:assert sha(ROOT/entry['path'])==entry['sha256'],entry['path']
checks=runpy.run_path(str(HERE/'verify-probes.py'))
checks['check_group']({'name':'class-selected-public-1','pairs':5,'full_proof':True})
meta=json.loads((HERE/'class-selected-direct-7.json').read_text())
assert meta['exit_code']==0 and not (HERE/meta['log']).read_bytes()
assert sha(HERE/meta['source'])==sha(ROOT/'lean/MicroCFTA/SourceCurrentClassSelectedChildLineage.lean')
checks['check_limits']('class-selected-direct-7')
print(json.dumps({'status':'PASS','entries':len(manifest['entries']),'public_pairs':5,'full_public_proof_output':True,'strict_empty':True,'general_outer_progress_still_open':True}))
