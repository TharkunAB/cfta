import hashlib
import importlib.util
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
manifest = json.loads((HERE / 'reader-observations-manifest.json').read_text())
for item in manifest['entries']:
    path = ROOT / item['path']
    assert path.is_file() and path.stat().st_size == item['bytes'], path
    assert hashlib.sha256(path.read_bytes()).hexdigest() == item['sha256'], path
selection = json.loads((HERE / 'reader-observations-selection.json').read_text())
assert selection['status'] == 'final'
assert selection['counts'] == {'public': 7, 'constructed': 0, 'auxiliary': 0}
spec = importlib.util.spec_from_file_location('checks', HERE / 'reader-observations-probe-check.py')
checks = importlib.util.module_from_spec(spec)
spec.loader.exec_module(checks)
for group in selection['groups']:
    checks.check_group(group)
for stem in [selection['strict'], selection['canonical'], *[g['name'] for g in selection['groups']]]:
    meta = json.loads((HERE / (stem + '.json')).read_text())
    assert meta['exit_code'] == 0, stem
    checks.check_limits(stem)
    assert meta['wrapper'][1:5] == ['--mem', '4G', '--time', '5m']
    if 'source' in meta:
        assert meta['sha256'] == hashlib.sha256((HERE / meta['source']).read_bytes()).hexdigest(), stem
strict = json.loads((HERE / (selection['strict'] + '.json')).read_text())
assert (HERE / strict['log']).read_bytes() == b''
source = ROOT / selection['production']
assert source.read_bytes() == (HERE / strict['source']).read_bytes()
assert hashlib.sha256(source.read_bytes()).hexdigest() == selection['sha256']
canonical = json.loads((HERE / (selection['canonical'] + '.json')).read_text())
log = (HERE / canonical['log']).read_text()
assert 'Build completed successfully (563 jobs).' in log
assert not re.search(r'\b(?:error|warning)(?:\([^)]*\))?:', log)
assert selection['failures'] == []
print(json.dumps({'status': 'PASS', 'entries': len(manifest['entries']), 'public_pairs': 7,
                  'constructed_pairs': 0, 'strict_log_bytes': 0, 'canonical_jobs': 563}))
