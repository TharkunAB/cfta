import hashlib
import json
import re
import runpy
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
sha = lambda path: hashlib.sha256(path.read_bytes()).hexdigest()
manifest = json.loads((HERE / 'tracked-union-manifest.json').read_text())
for item in manifest['files']:
    path = ROOT / item['path']
    assert path.stat().st_size == item['bytes'], path
    assert sha(path) == item['sha256'], path
selection = json.loads((HERE / 'tracked-union-selection.json').read_text())
checker = runpy.run_path(str(HERE / 'tracked-union-probe-check.py'))
for group in selection['groups']:
    checker['check_group'](group)
for stem in manifest['selected_executions']:
    meta = json.loads((HERE / (stem + '.json')).read_text())
    assert meta['exit_code'] == 0, stem
    assert meta['wrapper'][:5] == ['/home/tritlo/Code/heavy-management/bin/capped', '--mem', '4G', '--time', '5m'], stem
    assert 'leanprover--lean4---v4.34.1' in meta['command'][0], stem
    checker['check_limits'](stem)
    if 'source' in meta:
        assert sha(HERE / meta['source']) == meta['sha256'], stem
production = ROOT / selection['production']
strict = json.loads((HERE / (selection['strict'] + '.json')).read_text())
assert not (HERE / strict['log']).read_bytes()
assert production.read_bytes() == (HERE / strict['source']).read_bytes()
assert sha(production) == selection['sha256']
source = production.read_text()
assert re.findall(r'^theorem (\w+)', source, re.M) == ['union']
assert not re.findall(r'^def (\w+)', source, re.M)
assert '(ih : ∀ child ∈ expressions, Fusion bound child) : Fusion bound (.union expressions)' in source
assert source.count('SourceCurrentSourceChildDepth.union expressions') == 2
assert 'Nat.le_trans (firstOriginalBounds value member) firstDepth' in source
assert 'Nat.le_trans (secondOriginalBounds value member) secondDepth' in source
assert 'firstBounds raw List.mem_cons_self' in source
assert 'secondBounds other List.mem_cons_self' in source
assert source.count('SourceCurrentGeneratedUnionPreparation.prepare') == 2
assert source.count('SourceCurrentFilteredUnionCoverage.parts') == 3
assert 'coverage_nonopaque markers secondFinal' in source
assert 'reference_names markers secondFinal' in source
assert 'SourceCurrentTrackedRootProfile.mask_combine' in source
assert 'BinderFree' not in source
canonical = json.loads((HERE / (selection['canonical'] + '.json')).read_text())
log = (HERE / canonical['log']).read_text()
assert 'Build completed successfully' in log
assert not re.search(r'warning:|error:|sorryAx|failed to pretty print', log)
kernel = json.loads((HERE / (selection['constructed_strict'] + '.json')).read_text())
assert not (HERE / kernel['log']).read_bytes()
fixture = HERE / 'tracked-union-kernels.lean'
assert fixture.read_bytes() == (HERE / kernel['source']).read_bytes()
text = fixture.read_text()
start = text.index('private theorem checked :') + len('private theorem checked :')
public = text.index('theorem witness :') + len('theorem witness :')
assert text[start:text.index(' := by', start)] == text[public:text.index(' := checked', public)]
assert len(re.findall(r'^theorem ', text, re.M)) == 1
for required in ['SourceCurrentTrackedFilteredUnionFusion.union 0', 'used mu ∧ nested_used mu ∧ 0 < mu.depth',
    'expressions = [child,.var 3,child,.empty]', 'firstRaw.depth = 0 ∧ secondRaw.depth = 0',
    'execute (.reference firstOwn) firstMap reader = .done mu reader',
    'reader.nodes.next < (run (withoutSelfReference firstOwn firstChild) reader).2.nodes.next',
    'SourceCurrentTrackedRootProfile.observe markers (.reference marker : Value Nat Bool) = some [marker]',
    'SourceCurrentTrackedRootProfile.observe [] (.reference marker : Value Nat Bool) = none']:
    assert required in text, required
printed = json.loads((HERE / 'tracked-union-kernels-public-1.json').read_text())
assert (HERE / printed['source']).read_text().startswith(text)
assert not any('root-peaks' in item['path'] or 'root-run-check' in item['path'] for item in manifest['files'])
print(json.dumps(dict(status='PASS', files=len(manifest['files']), new_public_pairs=1,
    constructed_pairs=1, auxiliary_pairs=0, production_strict_log_bytes=0,
    constructed_strict_log_bytes=0, same_bound_union_composition=True,
    original_normalized_member_bounds_derived=True, output_depth_bounded=False,
    tracked_opacity_and_names_derived=True, general_binder_fusion_proved=False), sort_keys=True))
