import hashlib
import json
import re
import runpy
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


manifest = json.loads((HERE / 'fragment-contract-review-manifest.json').read_text())
for entry in manifest['files']:
    path = ROOT / entry['path']
    assert path.stat().st_size == entry['bytes'], path
    assert sha(path) == entry['sha256'], path
selection = json.loads((HERE / 'fragment-contract-review-selection.json').read_text())
assert selection['status'] == 'final'
assert selection['groups'] == []
checker = runpy.run_path(str(HERE / 'fragment-contract-review-probe-check.py'))
for group in selection['reused_groups']:
    checker['check_group'](group)
for stem in manifest['reviewed_executions']:
    meta = json.loads((HERE / (stem + '.json')).read_text())
    assert meta['exit_code'] == 0, stem
    assert meta['wrapper'][:5] == [
        '/home/tritlo/Code/heavy-management/bin/capped', '--mem', '4G', '--time', '5m'
    ], stem
    assert 'leanprover--lean4---v4.34.1' in meta['command'][0], stem
    checker['check_limits'](stem)
    if 'source' in meta:
        assert sha(HERE / meta['source']) == meta['sha256'], stem
for production, stem in selection['stricts'].items():
    meta = json.loads((HERE / (stem + '.json')).read_text())
    assert not (HERE / meta['log']).read_bytes(), stem
    assert (ROOT / production).read_bytes() == (HERE / meta['source']).read_bytes(), production
for stem in selection['constructed_stricts']:
    meta = json.loads((HERE / (stem + '.json')).read_text())
    assert not (HERE / meta['log']).read_bytes(), stem
for stem in selection['canonicals']:
    meta = json.loads((HERE / (stem + '.json')).read_text())
    log = (HERE / meta['log']).read_text()
    assert 'Build completed successfully (' in log, stem
    assert not re.search(r'warning:|error:|sorryAx|failed to pretty print', log), stem
pins = re.findall(r'^\| `([^`]+)` \| `([a-f0-9]{64})` \|$',
                  (HERE / 'fragment-contract-review-report.md').read_text(), re.M)
for path, expected in pins:
    assert sha(ROOT / path) == expected, path
print(json.dumps({
    'status': 'PASS', 'files': len(manifest['files']), 'source_pins': len(pins),
    'owned_public_pairs': 0, 'owned_constructed_pairs': 0, 'new_lean_runs': 0,
    'reused_public_pairs': 4, 'reused_constructed_pairs': 2,
    'selected_strict_logs': 5, 'strict_log_bytes': 0,
}, sort_keys=True))
