import hashlib
import json
import runpy
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
sha = lambda path: hashlib.sha256(path.read_bytes()).hexdigest()
manifest = json.loads((HERE / 'binder-contract-manifest.json').read_text())
for item in manifest['files']:
    path = ROOT / item['path']
    assert path.stat().st_size == item['bytes'], path
    assert sha(path) == item['sha256'], path
selection = json.loads((HERE / 'binder-contract-selection.json').read_text())
checker = runpy.run_path(str(HERE / 'binder-contract-probe-check.py'))
for group in selection['groups']:
    checker['check_group'](group)
for stem in [selection['strict']] + [g['name'] for g in selection['groups']]:
    meta = json.loads((HERE / (stem + '.json')).read_text())
    assert meta['exit_code'] == 0, stem
    assert meta['wrapper'][:5] == ['/home/tritlo/Code/heavy-management/bin/capped','--mem','4G','--time','5m']
    assert 'leanprover--lean4---v4.34.1' in meta['command'][0]
    assert sha(HERE / meta['source']) == meta['sha256']
    checker['check_limits'](stem)
strict = json.loads((HERE / (selection['strict'] + '.json')).read_text())
assert not (HERE / strict['log']).read_bytes()
source = (HERE / strict['source']).read_text()
assert source == (HERE / 'binder-contract-counterexample.lean').read_text()
assert 'private theorem ready : Ready reader := ⟨final_semantic,final_covered,final_open⟩' in source
assert 'private theorem body_law : SourceCurrentTrackedFilteredFusion.Fusion 0 body := by' in source
assert '¬ SourceCurrentBoundedFilteredFusion.Fusion 0 (.binder true expression)' in source
assert '¬ SourceCurrentTrackedFilteredFusion.Fusion 0 (.binder true expression)' in source
assert '(∀ rank < 0, ∀ term : Syntax Nat Bool, SourceCurrentTrackedFilteredFusion.Fusion rank term)' in source
assert 'first_done second_done whole.growth (first_keeps.trans last_keeps).growth first_filter second_filter first_warm second_warm' in source
assert source.count('\ntheorem ') == 1
assert 'sorry' not in source
public = json.loads((HERE / 'binder-contract-public-1.json').read_text())
assert (HERE / public['source']).read_text().startswith(source)
assert not any('root-peaks' in item['path'] or 'root-run-check' in item['path'] or 'root-capped-worker' in item['path'] for item in manifest['files'])
assert selection['canonical'] is None and selection['new_production'] == 0
print(json.dumps(dict(status='PASS',files=len(manifest['files']),new_production=0,constructed_pairs=1,
    full_all8_standard3=True,strict_log_bytes=0,exact_bounded_fusion_refuted=True,
    exact_tracked_fusion_refuted=True,strict_body_law_derived=True,
    causal_source_execution_defect_claimed=False),sort_keys=True))
