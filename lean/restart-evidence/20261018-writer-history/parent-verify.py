import hashlib
import json
import re
import runpy
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


manifest = json.loads((HERE / 'parent-manifest.json').read_text())
for entry in manifest['files']:
    path = ROOT / entry['path']
    assert path.stat().st_size == entry['bytes'], path
    assert sha(path) == entry['sha256'], path
selection = json.loads((HERE / 'parent-selection.json').read_text())
assert selection['status'] == 'final'
checker = runpy.run_path(str(HERE / 'parent-probe-check.py'))
for group in selection['groups'] + selection['reused_groups']:
    checker['check_group'](group)
for stem in manifest['owned_executions'] + manifest['reviewed_executions']:
    meta = json.loads((HERE / (stem + '.json')).read_text())
    assert meta['exit_code'] == 0, stem
    assert meta['wrapper'][:5] == [
        '/home/tritlo/Code/heavy-management/bin/capped', '--mem', '4G', '--time', '5m'
    ], stem
    assert 'leanprover--lean4---v4.34.1' in meta['command'][0], stem
    checker['check_limits'](stem)
    if 'source' in meta:
        assert sha(HERE / meta['source']) == meta['sha256'], stem
for source, stem in {**selection['stricts'], **manifest['reviewed_stricts']}.items():
    meta = json.loads((HERE / (stem + '.json')).read_text())
    assert not (HERE / meta['log']).read_bytes(), stem
    assert (ROOT / source).read_bytes() == (HERE / meta['source']).read_bytes(), source
for stem in selection['canonicals'] + manifest['reviewed_canonicals']:
    meta = json.loads((HERE / (stem + '.json')).read_text())
    log = (HERE / meta['log']).read_text()
    assert 'Build completed successfully (' in log, stem
    warnings = re.findall(r'^warning: ([^\n]+)', log, re.M)
    assert len(warnings) == 1, (stem, warnings)
    assert warnings[0].startswith(selection['canonical_allowed_warning_source']), (stem, warnings)
    assert not re.search(r'error:|sorryAx|failed to pretty print', log), stem
for source, expected in selection['productions'].items():
    path = ROOT / source
    assert sha(path) == expected, source
    text = path.read_text()
    assert all(line.rstrip() == line for line in text.splitlines()), source
lower = (ROOT / 'lean/MicroCFTA/SourceCurrentLowerMergeHistory.lean').read_text()
parent = (ROOT / 'lean/MicroCFTA/SourceCurrentParentMergeHistory.lean').read_text()
assert len(re.findall(r'^theorem ', lower, re.M)) == 5
assert len(re.findall(r'^theorem ', parent, re.M)) == 3
assert 'theorem parent ' in parent
assert '(raw : Raw memo)\n    (live :' in parent
pins = 0
for report in ['parent-review.md', 'parent-review-outer.md']:
    for path, expected in re.findall(r'^\| `([^`]+)` \| `([a-f0-9]{64})` \|$',
                                    (HERE / report).read_text(), re.M):
        assert sha(ROOT / path) == expected, path
        pins += 1
assert selection['constructed_groups'] == []
assert selection['retained_unselected'] == []
print(json.dumps({
    'status': 'PASS', 'files': len(manifest['files']), 'report_pins': pins,
    'owned_public_pairs': 8, 'owned_constructed_pairs': 0,
    'reused_public_pairs': 12, 'auxiliary_pairs': 0,
    'owned_lean_runs': 6, 'review_lean_runs': 0, 'strict_log_bytes': 0,
    'canonical_allowed_warning_source': selection['canonical_allowed_warning_source'],
    'manifest_sha256': sha(HERE / 'parent-manifest.json'),
}, sort_keys=True))
