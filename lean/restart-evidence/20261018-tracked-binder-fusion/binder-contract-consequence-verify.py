import hashlib
import json
import runpy
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
manifest = json.loads((HERE / 'binder-contract-consequence-manifest.json').read_text())
for item in manifest['files']:
    path = ROOT / item['path']
    assert path.stat().st_size == item['bytes']
    assert hashlib.sha256(path.read_bytes()).hexdigest() == item['sha256']
runpy.run_path(str(HERE / 'binder-contract-verify.py'),run_name='__main__')
print(json.dumps(dict(status='PASS',note_files=len(manifest['files']),new_lean_runs=0,new_proof_pairs=0)))
