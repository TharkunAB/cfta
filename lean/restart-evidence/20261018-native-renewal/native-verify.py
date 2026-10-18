import hashlib
import json
import re
import runpy
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


manifest = json.loads((HERE / 'native-manifest.json').read_text())
for entry in manifest['files']:
    path = ROOT / entry['path']
    assert path.stat().st_size == entry['bytes'], path
    assert sha(path) == entry['sha256'], path
selection = json.loads((HERE / 'native-selection.json').read_text())
assert selection['status'] == 'final'
checker = runpy.run_path(str(HERE / 'native-probe-check.py'))
for group in selection['groups']:
    checker['check_group'](group)
for stem in manifest['owned_executions']:
    meta = json.loads((HERE / (stem + '.json')).read_text())
    assert meta['wrapper'][:5] == [
        '/home/tritlo/Code/heavy-management/bin/capped', '--mem', '4G', '--time', '5m'
    ], stem
    assert 'leanprover--lean4---v4.34.1' in meta['command'][0], stem
    checker['check_limits'](stem)
    if 'source' in meta:
        assert sha(HERE / meta['source']) == meta['sha256'], stem
for stem in selection['selected_executions']:
    meta = json.loads((HERE / (stem + '.json')).read_text())
    assert meta['exit_code'] == 0, stem
for path, stem in selection['stricts'].items():
    meta = json.loads((HERE / (stem + '.json')).read_text())
    assert (ROOT / path).read_bytes() == (HERE / meta['source']).read_bytes(), path
    assert (HERE / meta['log']).stat().st_size == 0, stem
for stem in selection['canonicals']:
    meta = json.loads((HERE / (stem + '.json')).read_text())
    log = (HERE / meta['log']).read_text()
    warnings = re.findall(r'^warning: ([^\n]+)', log, re.M)
    assert len(warnings) == 1, (stem, warnings)
    assert warnings[0].startswith(selection['canonical_allowed_warning_source']), (stem, warnings)
    assert 'Build completed successfully (' in log, stem
    assert not re.search(r'error:|sorryAx|failed to pretty print', log), stem
for path, expected in selection['productions'].items():
    assert sha(ROOT / path) == expected, path
    text = (ROOT / path).read_text()
    assert len(re.findall(r'^theorem ', text, re.M)) == 1
    assert all(line.rstrip() == line for line in text.splitlines())
fixture = (HERE / 'native-kernels.lean').read_text()
private_statement = fixture.split('private theorem checked_witness :\n', 1)[1].split(' := by\n', 1)[0]
public_statement = fixture.split('theorem actual_cold_warm :\n', 1)[1].split(' := checked_witness', 1)[0]
assert private_statement == public_statement
assert len(re.findall(r'^theorem ', fixture, re.M)) == 1
for path, expected in selection['retained_attempt_exits'].items():
    meta = json.loads((HERE / (path + '.json')).read_text())
    assert meta['exit_code'] == expected
assert (HERE / 'native-kernels-direct-3.log').stat().st_size > 0
assert selection['counts'] == manifest['counts']
print(json.dumps({
    'status': 'PASS', 'files': len(manifest['files']),
    **selection['counts'], 'strict_log_bytes': 0,
    'full_public_groups': 2, 'exact_fixture_statement_alias': True,
    'manifest_sha256': sha(HERE / 'native-manifest.json'),
}, sort_keys=True))
