import hashlib
import json
import re
import runpy
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


manifest = json.loads((HERE / 'untouched-progress-manifest.json').read_text())
for item in manifest['files']:
    path = ROOT / item['path']
    assert path.stat().st_size == item['bytes'], path
    assert sha(path) == item['sha256'], path
selection = json.loads((HERE / 'untouched-progress-selection.json').read_text())
assert selection['status'] == 'final'
checker = runpy.run_path(str(HERE / 'untouched-progress-probe-check.py'))
for group in selection['groups']:
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
for stem in selection['retained_unselected']:
    meta = json.loads((HERE / (stem + '.json')).read_text())
    assert meta['exit_code'] == 1, stem
    assert sha(HERE / meta['source']) == meta['sha256'], stem
    checker['check_limits'](stem)
for stem in [selection['strict'], selection['constructed_strict']]:
    meta = json.loads((HERE / (stem + '.json')).read_text())
    assert (HERE / meta['log']).stat().st_size == 0, stem
strict = json.loads((HERE / (selection['strict'] + '.json')).read_text())
production = ROOT / selection['production']
assert production.read_bytes() == (HERE / strict['source']).read_bytes()
assert sha(production) == selection['sha256']
source = production.read_text()
assert re.findall(r'^theorem (\w+)', source, re.M) == ['walk_prefix', 'dispatch', 'budget']
assert all(line.rstrip() == line for line in source.splitlines())
canonical = json.loads((HERE / (selection['canonical'] + '.json')).read_text())
log = (HERE / canonical['log']).read_text()
assert 'Build completed successfully (1850 jobs).' in log
warnings = re.findall(r'^warning: (.*)$', log, re.M)
assert warnings == selection['canonical_warnings'], warnings
assert not re.search(r'error:|sorryAx|failed to pretty print', log)
fixture = (HERE / 'untouched-progress-kernels.lean').read_text()
selected_fixture = json.loads((HERE / (selection['constructed_strict'] + '.json')).read_text())
assert fixture == (HERE / selected_fixture['source']).read_text()
private_type = fixture.split('private theorem checked_witness :', 1)[1].split(' := by', 1)[0].strip()
public_type = fixture.split('theorem actual_dispatch :', 1)[1].split(' := checked_witness', 1)[0].strip()
assert private_type == public_type
assert '("root",.top) own [leaf,leaf,pair]' in fixture
assert '(parented.children.take 2)' in fixture
assert '(slot := 2) (nextSlot := 0)' in fixture
assert 'walk_done' not in fixture
assert 'private def walked' not in fixture
assert 'nodeCall ' not in fixture
assert selection['public_pairs'] == 3
assert selection['constructed_pairs'] == 1
assert selection['auxiliary_pairs'] == 0
print(json.dumps({
    'status': 'PASS', 'files': len(manifest['files']),
    'public_pairs': 3, 'constructed_pairs': 1, 'auxiliary_pairs': 0,
    'strict_log_bytes': [0, 0], 'canonical_warnings': warnings,
    'retained_failed_attempts': len(selection['retained_unselected']),
}, sort_keys=True))
