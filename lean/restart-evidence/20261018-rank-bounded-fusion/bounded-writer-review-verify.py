import hashlib
import json
import re
import runpy
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
sha = lambda path: hashlib.sha256(path.read_bytes()).hexdigest()
manifest = json.loads((HERE / 'bounded-writer-review-manifest.json').read_text())
for item in manifest['files']:
    path = ROOT / item['path']
    assert path.stat().st_size == item['bytes'], path
    assert sha(path) == item['sha256'], path
selection = json.loads((HERE / 'bounded-writer-review-selection.json').read_text())
assert selection['new_lean_jobs'] == selection['owned_public_pairs'] == selection['owned_constructed_pairs'] == 0
checker = runpy.run_path(str(HERE / 'bounded-writer-review-probe-check.py'))
for group in selection['groups']:
    checker['check_group'](group)
for stem in manifest['selected_executions']:
    meta = json.loads((HERE / (stem + '.json')).read_text())
    assert meta['exit_code'] == 0
    assert meta['wrapper'][:5] == ['/home/tritlo/Code/heavy-management/bin/capped', '--mem', '4G', '--time', '5m']
    assert 'leanprover--lean4---v4.34.1' in meta['command'][0]
    checker['check_limits'](stem)
    if 'source' in meta:
        assert sha(HERE / meta['source']) == meta['sha256']
production = ROOT / selection['production']
assert sha(production) == selection['sha256']
strict = json.loads((HERE / (selection['strict'] + '.json')).read_text())
assert not (HERE / strict['log']).read_bytes()
assert production.read_bytes() == (HERE / strict['source']).read_bytes()
canonical = json.loads((HERE / (selection['canonical'] + '.json')).read_text())
log = (HERE / canonical['log']).read_text()
assert 'Build completed successfully' in log
assert not re.search(r'warning:|error:|sorryAx|failed to pretty print', log)
kernel = json.loads((HERE / (selection['constructed_strict'] + '.json')).read_text())
assert not (HERE / kernel['log']).read_bytes()
previous = json.loads((HERE / (selection['prior_warning_strict'] + '.json')).read_text())
assert (HERE / previous['log']).stat().st_size == 1159
assert 'warning:' in (HERE / previous['log']).read_text()
assert previous['sha256'] == 'cf8c236f037c1fb12f7125f86d3698e0ba9cfd65e820129257cf6ae74da7d705'
old_source = (HERE / previous['source']).read_text()
assert old_source.replace('private theorem callback_replay [DecidableEq (EdgeKey Symbol Guard)]',
    'private theorem callback_replay') == production.read_text()
old_canonical = json.loads((HERE / (selection['prior_warning_canonical'] + '.json')).read_text())
assert 'warning:' in (HERE / old_canonical['log']).read_text()
source = production.read_text()
assert re.findall(r'^theorem (\w+)', source, re.M) == ['publication', 'writer']
assert 'smaller : ∀ rank < value.depth, ∀ expression : Syntax Symbol Guard, Fusion rank expression' in source
assert 'SourceCurrentPublicationSharedReplacements.substitutions' in source
fixture = (HERE / kernel['source']).read_text()
assert 'SourceCurrentBoundedWriterFusion.publication event final cut_current body_current smaller' in fixture
assert 'environment (.interned 0) = some .empty' in fixture
assert 'SourceCurrentFilteredBinderFreeFusion.source event.expression' in fixture
assert not any('root-peaks' in item['path'] or 'root-run-check' in item['path'] for item in manifest['files'])
assert not any(item['path'].endswith('/bounded-writer-kernels.lean') for item in manifest['files'])
print(json.dumps(dict(status='PASS', files=len(manifest['files']), new_lean_jobs=0,
    owned_public_pairs=0, owned_constructed_pairs=0, reused_public_pairs=2,
    reused_constructed_pairs=1, mathematical_issues=0, validation_warning_fixed=True,
    unresolved_validation_issues=0, uniform_smaller_source_hypothesis_proved=False,
    outer_symbolic_lower_proved=False), sort_keys=True))
