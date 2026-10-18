import hashlib
import json
import re
import runpy
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


manifest = json.loads((HERE / 'causal-cross-local-integration-manifest.json').read_text())
for item in manifest['files']:
    path = ROOT / item['path']
    assert path.stat().st_size == item['bytes'], path
    assert sha(path) == item['sha256'], path
selection = json.loads((HERE / 'causal-cross-local-integration-selection.json').read_text())
assert selection['status'] == 'final'
checker = runpy.run_path(str(HERE / 'causal-cross-local-integration-probe-check.py'))
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
strict = json.loads((HERE / (selection['strict'] + '.json')).read_text())
assert (HERE / strict['log']).stat().st_size == 0
working = HERE / selection['working']
assert working.read_bytes() == (HERE / strict['source']).read_bytes()
assert sha(working) == selection['sha256']
source = working.read_text()
assert len(re.findall(r'^theorem ', source, re.M)) == 1
assert all(line.rstrip() == line for line in source.splitlines())
claim = source.split('private def Claim : Prop :=\n  ', 1)[1].split('\n\nprivate theorem checked', 1)[0]
public = source.split('theorem witness :\n  ', 1)[1].split(' := checked', 1)[0]
assert claim == public
for production in selection['reviewed_production']:
    path = ROOT / production['path']
    meta = json.loads((HERE / (production['strict'] + '.json')).read_text())
    assert not (HERE / meta['log']).read_bytes(), production
    assert path.read_bytes() == (HERE / meta['source']).read_bytes(), production
    assert sha(path) == production['sha256'], production
    canonical = json.loads((HERE / (production['canonical'] + '.json')).read_text())
    log = (HERE / canonical['log']).read_text()
    assert 'Build completed successfully (' + str(production['jobs']) + ' jobs).' in log
    assert not re.search(r'warning:|error:|sorryAx|failed to pretty print', log)
for attempt in selection['retained_unselected']:
    meta = json.loads((HERE / (attempt['stem'] + '.json')).read_text())
    assert meta['exit_code'] == attempt['exit_code'], attempt['stem']
print(json.dumps({
    'status': 'PASS', 'files': len(manifest['files']),
    'public_pairs': 0, 'constructed_pairs': 1, 'auxiliary_pairs': 0,
    'reused_public_pairs': 2, 'strict_log_bytes': 0,
    'private_public_statement_identical': True,
}, sort_keys=True))
