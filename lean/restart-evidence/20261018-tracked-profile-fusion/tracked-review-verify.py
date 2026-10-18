import hashlib
import json
import re
import runpy
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
sha = lambda path: hashlib.sha256(path.read_bytes()).hexdigest()
manifest = json.loads((HERE / 'tracked-review-manifest.json').read_text())
for item in manifest['files']:
    path = ROOT / item['path']
    assert path.stat().st_size == item['bytes'], path
    assert sha(path) == item['sha256'], path
selection = json.loads((HERE / 'tracked-review-selection.json').read_text())
checker = runpy.run_path(str(HERE / 'tracked-review-probe-check.py'))
for group in selection['groups']:
    checker['check_group'](group)
for source in selection['production']:
    path = ROOT / source['path']
    assert sha(path) == source['sha256']
    meta = json.loads((HERE / (source['strict'] + '.json')).read_text())
    assert meta['exit_code'] == 0
    assert not (HERE / meta['log']).read_bytes(), source['strict']
    assert path.read_bytes() == (HERE / meta['source']).read_bytes()
    checker['check_limits'](source['strict'])
    canonical = json.loads((HERE / (source['canonical'] + '.json')).read_text())
    assert canonical['exit_code'] == 0
    log = (HERE / canonical['log']).read_text()
    assert 'Build completed successfully' in log
    assert not re.search(r'warning:|error:|sorryAx|failed to pretty print', log)
    checker['check_limits'](source['canonical'])
for strict in selection['constructed_strict']:
    meta = json.loads((HERE / (strict + '.json')).read_text())
    assert meta['exit_code'] == 0
    assert not (HERE / meta['log']).read_bytes(), strict
    assert sha(HERE / meta['source']) == meta['sha256']
    checker['check_limits'](strict)
for group in selection['groups']:
    meta = json.loads((HERE / (group['name'] + '.json')).read_text())
    assert meta['wrapper'][:5] == ['/home/tritlo/Code/heavy-management/bin/capped','--mem','4G','--time','5m']
    assert 'leanprover--lean4---v4.34.1' in meta['command'][0]
assert not any('root-peaks' in item['path'] or 'root-run-check' in item['path'] or 'root-capped-worker' in item['path'] for item in manifest['files'])
assert selection['new_lean_runs'] == selection['owned_public_pairs'] == selection['owned_constructed_pairs'] == 0
print(json.dumps(dict(status='PASS', files=len(manifest['files']), new_lean_runs=0, owned_public_pairs=0,
    owned_constructed_pairs=0, reused_public_pairs=sum(g['pairs'] for g in selection['groups'] if g['kind']=='reused-public'),
    reused_constructed_pairs=sum(g['pairs'] for g in selection['groups'] if g['kind']=='reused-constructed'),
    material_issue_found=False, full_binder_fusion_proved=False),sort_keys=True))
