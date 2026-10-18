import ast
import json
import re
import runpy
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]


def read(name):
    return json.loads((HERE / name).read_text())


checks = runpy.run_path(str(HERE / 'verify-probes.py'))
assert read('selection-status.json')['finalized']
groups = read('selected-groups.json')
assert len({group['name'] for group in groups}) == len(groups)
counts = {kind: sum(group['pairs'] for group in groups if group['kind'] == kind)
          for kind in ['new-public', 'constructed', 'private-claim']}
assert counts == read('expected-counts.json')['pairs']
for group in groups:
    checks['check_group'](group)
modules = read('frozen-modules.json')
assert len(modules) == read('expected-counts.json')['modules']
for module, expected in modules.items():
    assert checks['sha'](ROOT / 'lean/MicroCFTA' / (module + '.lean')) == expected
for module, stem in read('selected-strict.json').items():
    receipt = read(stem + '.json')
    assert receipt['exit_code'] == 0 and not (HERE / receipt['log']).read_bytes()
    assert checks['sha'](HERE / receipt['source']) == modules[module]
    checks['check_limits'](stem)
stricts = read('selected-constructed-strict.json')
assert len(stricts) == read('expected-counts.json')['constructed_strict']
for stem, working in stricts.items():
    receipt = read(stem + '.json')
    assert receipt['exit_code'] == 0 and not (HERE / receipt['log']).read_bytes()
    assert checks['sha'](HERE / receipt['source']) == receipt['sha256']
    assert checks['sha'](HERE / receipt['source']) == checks['sha'](HERE / working)
    checks['check_limits'](stem)
old_log = (ROOT / 'lean/restart-evidence/20261018-selected-read-producers/full-audit-1.log').read_text()
old_warnings = re.findall(r'^warning:.*$', old_log, re.M)
for module, stem in read('selected-canonical.json').items():
    receipt = read(stem + '.json')
    log = (HERE / receipt['log']).read_text()
    assert receipt['exit_code'] == 0 and 'Build completed successfully' in log
    expected = old_warnings if module in ['SourceCurrentAllocatedEqualityAbsorption', 'SourceCurrentOuterEffectiveGain', 'SourceCurrentOuterUntouchedProgress'] else []
    assert re.findall(r'^warning:.*$', log, re.M) == expected
    checks['check_limits'](stem)
components = read('component-manifests.json')
assert len(components) == read('expected-counts.json')['components']
entries = 0
for name in components:
    for entry in read(name).get('entries', read(name).get('files', [])):
        path = ROOT / entry['path']
        assert checks['sha'](path) == entry['sha256'], (name, entry['path'])
        if 'bytes' in entry:
            assert path.stat().st_size == entry['bytes']
        entries += 1
progress_pins = read('progress-review-source-pins.json')['files']
for entry in progress_pins:
    path = ROOT / entry['path']
    assert checks['sha'](path) == entry['sha256'], entry['path']
    assert path.stat().st_size == entry['bytes']
assert len(progress_pins) == 19
audit = read('selected-audit.json')
receipt = read(audit['name'] + '.json')
assert receipt['exit_code'] == 0
checks['check_limits'](audit['name'])
log = (HERE / receipt['log']).read_text()
assert re.findall(r'^warning:.*$', log, re.M) == old_warnings
jobs = int(re.findall(r'Build completed successfully \((\d+) jobs\)\.', log)[-1])
dependencies = int(re.findall(r'Checked axiom dependencies of (\d+) MicroCFTA theorems\.', log)[-1])
assert jobs == audit['jobs'] == 3413 + len(modules) and dependencies == audit['dependency_checks']
peaks = [int(re.search(r' (\d+)M 0$', line).group(1))
         for line in (HERE / 'root-peaks.txt').read_text().splitlines() if re.search(r' (\d+)M 0$', line)]
for path in HERE.glob('*.py'):
    ast.parse(path.read_text(), filename=str(path))
print(json.dumps({
 'status':'PASS','proof_commit':(HERE/'proof-commit.txt').read_text().strip(),
 'production_modules':modules,'new_public_pairs':counts['new-public'],
 'constructed_pairs':counts['constructed'],'private_claim_pairs':counts['private-claim'],
 'groups':len(groups),'full_public_proofs_and_standard_axioms':True,
 'strict_empty_logs':len(modules)+len(stricts),'component_manifests':components,
 'component_entries':entries,'progress_review_source_pins':len(progress_pins),'audit_jobs':jobs,'audit_dependency_checks':dependencies,
 'old_warnings':old_warnings,'memory_max':'4294967296','memory_high':'4294967296','swap_max':'0',
 'successful_root_job_peak_upper_bound_MiB':max(peaks),
 'normalization_absorbs_arbitrary_covered_own_classes_with_exact_order':True,
 'actual_cold_and_warm_combination_returns_same_complete_inherited_value':True,
 'covered_prefix_descent_strictness_requires_nonempty_inheritance':True,
 'actual_height_gain_derives_new_distinct_own_pair_not_in_inherited_component':True,
 'new_pair_preserves_exact_original_row_and_nonempty_owner_receipts':True,
 'busy_fault_is_not_excluded_by_a_necessary_gain_witness':True,
 'unfinished_dispatch_uses_only_completed_earlier_siblings':True,
 'untouched_anchor_chain_allows_changing_indices_and_explicit_footprints':True,
 'three_actual_constructed_heads_are_checked':True,
 'renewal_of_dropped_constraint_origins_is_not_yet_bounded':True,
 'empty_owner_busy_exclusion_still_open':True,
 'broad_constructed_root_and_exact_query_claims_are_unchanged':True,
 'general_recursive_completion_and_convergence_still_open':True,
 'public_haskell_correspondence_still_open':True,'new_haskell_behavior_patch':False,
},indent=2))
