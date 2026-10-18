import hashlib
import json
import re
import runpy
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


manifest = json.loads((HERE / 'guard-manifest.json').read_text())
for entry in manifest['files']:
    path = ROOT / entry['path']
    assert path.stat().st_size == entry['bytes'], path
    assert sha(path) == entry['sha256'], path
selection = json.loads((HERE / 'guard-selection.json').read_text())
assert selection['status'] == 'final'
checker = runpy.run_path(str(HERE / 'guard-probe-check.py'))
for group in selection['groups']:
    checker['check_group'](group)
for stem in manifest['executions']:
    meta = json.loads((HERE / (stem + '.json')).read_text())
    assert meta['wrapper'][:5] == [
        '/home/tritlo/Code/heavy-management/bin/capped', '--mem', '4G', '--time', '5m'
    ], stem
    assert 'leanprover--lean4---v4.34.1' in meta['command'][0], stem
    checker['check_limits'](stem)
    if 'source' in meta:
        assert sha(HERE / meta['source']) == meta['sha256'], stem
    if stem in selection['retained_unselected']:
        assert meta['exit_code'] == 1, stem
    else:
        assert meta['exit_code'] == 0, stem
strict = json.loads((HERE / (selection['strict'] + '.json')).read_text())
assert not (HERE / strict['log']).read_bytes()
production = ROOT / selection['production']
assert production.read_bytes() == (HERE / strict['source']).read_bytes()
assert sha(production) == selection['sha256']
canonical = json.loads((HERE / (selection['canonical'] + '.json')).read_text())
log = (HERE / canonical['log']).read_text()
assert 'Build completed successfully (1050 jobs).' in log
warnings = re.findall(r'^warning: ([^\n]+)', log, re.M)
assert len(warnings) == 1, warnings
assert warnings[0].startswith(selection['canonical_allowed_warning_source']), warnings
assert not re.search(r'error:|sorryAx|failed to pretty print', log)
source = production.read_text()
assert len(re.findall(r'^theorem ', source, re.M)) == 1
assert 'theorem live_pair_lost :' in source
assert 'some [],.not .bottom' in source
assert all(line.rstrip() == line for line in source.splitlines())
report = (HERE / 'guard-review.md').read_text()
pins = re.findall(r'^\| `([^`]+)` \| `([a-f0-9]{64})` \|$', report, re.M)
assert len(pins) == 6
for path, expected in pins:
    assert sha(ROOT / path) == expected, path
assert not list(HERE.glob('guard-__pycache__'))
print(json.dumps({
    'status': 'PASS', 'files': len(manifest['files']), 'report_pins': len(pins),
    'public_pairs': 1, 'constructed_pairs': 0, 'reused_pairs': 0,
    'auxiliary_pairs': 0, 'new_lean_executions': 4,
    'strict_log_bytes': 0, 'canonical_warnings': warnings,
    'manifest_sha256': sha(HERE / 'guard-manifest.json'),
}, sort_keys=True))
