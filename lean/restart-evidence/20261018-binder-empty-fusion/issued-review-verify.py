import hashlib
import json
import re
import runpy
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
sha = lambda path: hashlib.sha256(path.read_bytes()).hexdigest()
manifest = json.loads((HERE / 'issued-review-manifest.json').read_text())
for item in manifest['files']:
    path = ROOT / item['path']
    assert path.stat().st_size == item['bytes'], path
    assert sha(path) == item['sha256'], path
selection = json.loads((HERE / 'issued-review-selection.json').read_text())
assert selection['new_lean_jobs'] == selection['owned_public_pairs'] == selection['owned_constructed_pairs'] == 0
checker = runpy.run_path(str(HERE / 'issued-review-probe-check.py'))
for group in selection['groups']:
    checker['check_group'](group)
for production in selection['productions']:
    source = ROOT / production['path']
    assert sha(source) == production['sha256']
    strict = json.loads((HERE / (production['strict'] + '.json')).read_text())
    assert strict['exit_code'] == 0
    assert not (HERE / strict['log']).read_bytes()
    assert source.read_bytes() == (HERE / strict['source']).read_bytes()
    checker['check_limits'](production['strict'])
    canonical = json.loads((HERE / (production['canonical'] + '.json')).read_text())
    log = (HERE / canonical['log']).read_text()
    assert canonical['exit_code'] == 0
    assert 'Build completed successfully' in log
    assert not re.search(r'warning:|error:|sorryAx|failed to pretty print', log)
    checker['check_limits'](production['canonical'])
for stem in selection['constructed_strict']:
    meta = json.loads((HERE / (stem + '.json')).read_text())
    assert meta['exit_code'] == 0
    assert not (HERE / meta['log']).read_bytes()
    checker['check_limits'](stem)
for stem in manifest['selected_executions']:
    meta = json.loads((HERE / (stem + '.json')).read_text())
    assert meta['exit_code'] == 0
    assert meta['wrapper'][:5] == ['/home/tritlo/Code/heavy-management/bin/capped', '--mem', '4G', '--time', '5m']
    assert 'leanprover--lean4---v4.34.1' in meta['command'][0]
    if 'source' in meta:
        assert sha(HERE / meta['source']) == meta['sha256']
assert not any('root-peaks' in item['path'] or 'root-run-check' in item['path'] for item in manifest['files'])
assert all(not item['path'].endswith('issued-writers-kernels.lean') and
    not item['path'].endswith('issued-history-kernels.lean') for item in manifest['files'])
print(json.dumps(dict(status='PASS', files=len(manifest['files']), new_lean_jobs=0,
    owned_public_pairs=0, owned_constructed_pairs=0, reused_public_pairs=15,
    reused_constructed_pairs=2, material_issues=0, final_ready_explicit=True,
    full_binder_fusion_proved=False), sort_keys=True))
