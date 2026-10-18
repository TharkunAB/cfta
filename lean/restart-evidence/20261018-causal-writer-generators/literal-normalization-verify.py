import hashlib
import json
import re
import runpy
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


manifest = json.loads((HERE / 'literal-normalization-manifest.json').read_text())
for entry in manifest['files']:
    path = ROOT / entry['path']
    assert path.stat().st_size == entry['bytes'], path
    assert sha(path) == entry['sha256'], path
selection = json.loads((HERE / 'literal-normalization-selection.json').read_text())
assert selection['status'] == 'final'
checker = runpy.run_path(str(HERE / 'literal-normalization-probe-check.py'))
for group in selection['groups'] + selection['reused_groups']:
    checker['check_group'](group)
for stem in manifest['selected_executions'] + manifest['reviewed_executions']:
    meta = json.loads((HERE / (stem + '.json')).read_text())
    assert meta['exit_code'] == 0, stem
    assert meta['wrapper'][:5] == [
        '/home/tritlo/Code/heavy-management/bin/capped', '--mem', '4G', '--time', '5m'
    ], stem
    assert 'leanprover--lean4---v4.34.1' in meta['command'][0], stem
    checker['check_limits'](stem)
    if 'source' in meta:
        assert sha(HERE / meta['source']) == meta['sha256'], stem
for production, stem in manifest['stricts'].items():
    meta = json.loads((HERE / (stem + '.json')).read_text())
    assert not (HERE / meta['log']).read_bytes(), stem
    assert (ROOT / production).read_bytes() == (HERE / meta['source']).read_bytes(), production
for stem in manifest['canonicals']:
    meta = json.loads((HERE / (stem + '.json')).read_text())
    log = (HERE / meta['log']).read_text()
    assert 'Build completed successfully (' in log, stem
    assert not re.search(r'warning:|error:|sorryAx|failed to pretty print', log), stem
production = ROOT / selection['production']
assert sha(production) == selection['sha256']
source = production.read_text()
assert len(re.findall(r'^def ', source, re.M)) == 1
assert len(re.findall(r'^theorem ', source, re.M)) == 3
assert all(line.rstrip() == line for line in source.splitlines())
assert selection['retained_unselected'] == []
pins = 0
for report in ['writer-progress-review.md', 'writer-next-review.md']:
    for path, expected in re.findall(r'^\| `([^`]+)` \| `([a-f0-9]{64})` \|$',
                                    (HERE / report).read_text(), re.M):
        assert sha(ROOT / path) == expected, path
        pins += 1
print(json.dumps({
    'status': 'PASS', 'files': len(manifest['files']), 'report_pins': pins,
    'public_pairs': 4, 'constructed_pairs': 0, 'auxiliary_pairs': 0,
    'reused_public_pairs': 8, 'strict_log_bytes': 0,
    'canonical_warnings': [], 'new_lean_executions': 3,
}, sort_keys=True))
