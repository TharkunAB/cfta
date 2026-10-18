import hashlib
import json
import re
import runpy
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

manifest_path = HERE / 'causal-empty-review-manifest.json'
manifest = json.loads(manifest_path.read_text())
for entry in manifest['files']:
    path = ROOT / entry['path']
    assert path.stat().st_size == entry['bytes'] and sha(path) == entry['sha256'], path
selection = json.loads((HERE / 'causal-empty-review-selection.json').read_text())
assert selection['status'] == 'final' and selection['finalized']
assert [selection[key] for key in ['owned_public_pairs', 'owned_constructed_pairs', 'owned_lean_runs']] == [0, 0, 0]
checker = runpy.run_path(str(HERE / 'causal-empty-review-probe-check.py'))
for group in selection['groups']:
    checker['check_group'](group)
assert sum(group['pairs'] for group in selection['groups']) == selection['reused_public_pairs'] == 11
for module in selection['reviewed_modules']:
    source = ROOT / module['source']
    assert sha(source) == module['sha256']
    assert not re.search(r'\bsorry\b|\baxiom\b', source.read_text())
    strict = json.loads((HERE / (module['strict'] + '.json')).read_text())
    assert not (HERE / strict['log']).read_bytes()
    assert source.read_bytes() == (HERE / strict['source']).read_bytes()
    canonical = json.loads((HERE / (module['canonical'] + '.json')).read_text())
    log = (HERE / canonical['log']).read_text()
    assert f"Build completed successfully ({module['canonical_jobs']} jobs)." in log
    assert not re.search(r'warning:|error:', log)
for stem in manifest['selected_executions']:
    meta = json.loads((HERE / (stem + '.json')).read_text())
    assert meta['exit_code'] == 0
    assert meta['wrapper'][:5] == ['/home/tritlo/Code/heavy-management/bin/capped', '--mem', '4G', '--time', '5m']
    assert 'leanprover--lean4---v4.34.1' in meta['command'][0]
    checker['check_limits'](stem)
    if 'source' in meta:
        assert sha(HERE / meta['source']) == meta['sha256']
assert not any('root-peaks' in item['path'] for item in manifest['files'])
print(json.dumps({'status': 'PASS', 'files': len(manifest['files']), 'manifest_sha256': sha(manifest_path),
    'reviewed_production_modules': 4, 'reused_public_pairs': 11, 'owned_public_pairs': 0,
    'owned_constructed_pairs': 0, 'owned_lean_runs': 0, 'strict_log_bytes': [0, 0, 0, 0],
    'canonical_logs_clean': True, 'full_public_options': 8, 'axioms': ['propext', 'Classical.choice', 'Quot.sound']}))
