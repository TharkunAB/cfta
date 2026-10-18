import hashlib
import json
import re
import runpy
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


manifest = json.loads((HERE / 'cold-mu-manifest.json').read_text())
for item in manifest['files']:
    path = ROOT / item['path']
    assert path.stat().st_size == item['bytes'], path
    assert sha(path) == item['sha256'], path
selection = json.loads((HERE / 'cold-mu-selection.json').read_text())
assert selection['status'] == 'final'
checker = runpy.run_path(str(HERE / 'cold-mu-probe-check.py'))
for group in selection['groups'] + selection['reused_groups']:
    checker['check_group'](group)
for stem in manifest['selected_executions']:
    meta = json.loads((HERE / (stem + '.json')).read_text())
    assert meta['exit_code'] == 0, stem
    assert meta['wrapper'][:5] == [
        '/home/tritlo/Code/heavy-management/bin/capped', '--mem', '4G', '--time', '5m'
    ], stem
    assert 'leanprover--lean4---v4.34.1' in meta['command'][0], stem
    checker['check_limits'](stem)
    if 'source' in meta:
        assert sha(HERE / meta['source']) == meta['sha256'], stem
for stem in selection['owned_executions']:
    meta = json.loads((HERE / (stem + '.json')).read_text())
    checker['check_limits'](stem)
    assert sha(HERE / meta['source']) == meta['sha256'], stem
for attempt in selection['retained_unselected']:
    meta = json.loads((HERE / (attempt['stem'] + '.json')).read_text())
    assert meta['exit_code'] == attempt['exit_code'], attempt
for item in selection['reviewed_productions']:
    path = ROOT / item['path']
    assert sha(path) == item['sha256'], path
    strict = json.loads((HERE / (item['strict'] + '.json')).read_text())
    assert path.read_bytes() == (HERE / strict['source']).read_bytes(), path
    assert (HERE / strict['log']).stat().st_size == 0, strict
    canonical = json.loads((HERE / (item['canonical'] + '.json')).read_text())
    log = (HERE / canonical['log']).read_text()
    assert 'Build completed successfully' in log, canonical
    assert not re.search(r'warning:|error:|sorryAx', log), canonical
strict = json.loads((HERE / (selection['constructed_strict'] + '.json')).read_text())
assert (HERE / strict['log']).stat().st_size == 0
source = (HERE / strict['source']).read_text()
assert (HERE / 'cold-mu-kernels.lean').read_text() == source
assert len(re.findall(r'^theorem ', source, re.M)) == 1
checked = source.split('private theorem checked :', 1)[1].split(' := by', 1)[0]
public = source.split('theorem cold_nested_mu :', 1)[1].split(' := checked', 1)[0]
assert checked == public, 'exact-statement alias'
for pin in json.loads((HERE / 'cold-mu-source-pins.json').read_text()):
    assert sha(ROOT / pin['path']) == pin['sha256'], pin
assert not list(HERE.glob('cold-mu-*.pyc'))
print(json.dumps({
    'status': 'PASS', 'files': len(manifest['files']),
    'owned_public_pairs': 0, 'owned_constructed_pairs': 1,
    'reused_public_pairs': 4, 'reused_constructed_pairs': 0,
    'owned_lean_runs': 8, 'selected_constructed_strict_bytes': 0,
    'reviewed_production_strict_bytes': [0, 0, 0],
    'canonical_warnings': [], 'full_groups': 4,
    'exact_statement_alias': True,
}, sort_keys=True))
