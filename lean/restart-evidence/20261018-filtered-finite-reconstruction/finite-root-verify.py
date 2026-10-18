import hashlib
import importlib.util
import json
import os
from pathlib import Path

os.environ['PYTHONDONTWRITEBYTECODE'] = '1'
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
manifest = json.loads((HERE / 'finite-root-manifest.json').read_text())
for entry in manifest['files']:
    path = ROOT / entry['path']
    assert path.stat().st_size == entry['bytes'], entry['path']
    assert hashlib.sha256(path.read_bytes()).hexdigest() == entry['sha256'], entry['path']
selection = json.loads((HERE / 'finite-root-selection.json').read_text())
spec = importlib.util.spec_from_file_location('finite_root_probe_check', HERE / 'finite-root-probe-check.py')
checker = importlib.util.module_from_spec(spec)
spec.loader.exec_module(checker)
for group in selection['groups']:
    checker.check_group(group)
strict = selection['strict']
meta = json.loads((HERE / (strict + '.json')).read_text())
assert meta['exit_code'] == 0
assert not (HERE / meta['log']).read_bytes()
assert (ROOT / selection['production']).read_bytes() == (HERE / meta['source']).read_bytes()
checker.check_limits(strict)
canonical = json.loads((HERE / (selection['canonical'] + '.json')).read_text())
assert canonical['exit_code'] == 0
log = (HERE / canonical['log']).read_text()
assert 'warning' not in log and 'error:' not in log
checker.check_limits(selection['canonical'])
print(json.dumps({'status':'PASS','files':len(manifest['files']),'public_pairs':2,'constructed_pairs':0,'strict_modules':1}))
