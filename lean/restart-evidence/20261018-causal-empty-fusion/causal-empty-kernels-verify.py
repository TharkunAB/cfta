import hashlib
import json
import re
import runpy
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

manifest = json.loads((HERE / 'causal-empty-kernels-manifest.json').read_text())
for item in manifest['files']:
    path = ROOT / item['path']
    assert path.stat().st_size == item['bytes'], path
    assert sha(path) == item['sha256'], path
selection = json.loads((HERE / 'causal-empty-kernels-selection.json').read_text())
assert selection['status'] == 'final'
checker = runpy.run_path(str(HERE / 'causal-empty-kernels-probe-check.py'))
for group in selection['groups']:
    checker['check_group'](group)
for stem in manifest['selected_executions']:
    meta = json.loads((HERE / (stem + '.json')).read_text())
    assert meta['exit_code'] == 0, stem
    assert meta['wrapper'][:5] == [
        '/home/tritlo/Code/heavy-management/bin/capped', '--mem', '4G', '--time', '5m'
    ], stem
    assert 'leanprover--lean4---v4.34.1' in meta['command'][0], stem
    assert sha(HERE / meta['source']) == meta['sha256'], stem
    checker['check_limits'](stem)
strict = json.loads((HERE / (selection['strict'] + '.json')).read_text())
assert (HERE / strict['log']).stat().st_size == 0
fixture = ROOT / selection['fixture']
assert fixture.read_bytes() == (HERE / strict['source']).read_bytes()
assert sha(fixture) == selection['sha256']
source = fixture.read_text()
assert len(re.findall(r'^theorem ', source, re.M)) == 1
assert 'SourceCurrentCausalFilteredSourceFusion.source expression' in source
assert 'Calls a b ∧ Calls .empty .empty' in source
assert all(line.rstrip() == line for line in source.splitlines())
probe = json.loads((HERE / (selection['constructed_group'] + '.json')).read_text())
assert (HERE / probe['source']).read_text().startswith(source)
for attempt in selection['retained_unselected']:
    meta = json.loads((HERE / (attempt['stem'] + '.json')).read_text())
    assert meta['exit_code'] == attempt['exit_code'], attempt['stem']
print(json.dumps({
    'status': 'PASS', 'files': len(manifest['files']),
    'public_pairs': 0, 'constructed_pairs': 1, 'auxiliary_pairs': 0,
    'strict_log_bytes': 0,
}, sort_keys=True))
