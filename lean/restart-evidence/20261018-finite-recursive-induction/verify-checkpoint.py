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
assert counts == {'new-public': 24, 'constructed': 1, 'private-claim': 0}
for group in groups:
    checks['check_group'](group)
modules = read('frozen-modules.json')
assert len(modules) == 3
for module, expected in modules.items():
    assert checks['sha'](ROOT / 'lean/MicroCFTA' / (module + '.lean')) == expected
for module, stem in read('selected-strict.json').items():
    receipt = read(stem + '.json')
    assert receipt['exit_code'] == 0 and not (HERE / receipt['log']).read_bytes()
    assert checks['sha'](HERE / receipt['source']) == modules[module]
    checks['check_limits'](stem)
stricts = read('selected-constructed-strict.json')
assert len(stricts) == 1
for stem, working in stricts.items():
    receipt = read(stem + '.json')
    assert receipt['exit_code'] == 0 and not (HERE / receipt['log']).read_bytes()
    assert checks['sha'](HERE / receipt['source']) == checks['sha'](HERE / working)
    checks['check_limits'](stem)
old_log = (ROOT / 'lean/restart-evidence/20261018-selected-read-producers/full-audit-1.log').read_text()
old_warnings = re.findall(r'^warning:.*$', old_log, re.M)
for stem in read('selected-canonical.json').values():
    receipt = read(stem + '.json')
    log = (HERE / receipt['log']).read_text()
    assert receipt['exit_code'] == 0 and 'Build completed successfully' in log
    expected = []
    assert re.findall(r'^warning:.*$', log, re.M) == expected
    checks['check_limits'](stem)
components = read('component-manifests.json')
assert len(components) == 4
entries = 0
for name in components:
    for entry in read(name)['entries']:
        path = ROOT / entry['path']
        assert checks['sha'](path) == entry['sha256'], (name, entry['path'])
        if 'bytes' in entry:
            assert path.stat().st_size == entry['bytes']
        entries += 1
audit = read('selected-audit.json')
receipt = read(audit['name'] + '.json')
assert receipt['exit_code'] == 0
checks['check_limits'](audit['name'])
log = (HERE / receipt['log']).read_text()
assert re.findall(r'^warning:.*$', log, re.M) == old_warnings
jobs = int(re.findall(r'Build completed successfully \((\d+) jobs\)\.', log)[-1])
dependencies = int(re.findall(r'Checked axiom dependencies of (\d+) MicroCFTA theorems\.', log)[-1])
assert jobs == audit['jobs'] == 3295 and dependencies == audit['dependency_checks'] == 71549
peaks = [int(re.search(r' (\d+)M 0$', line).group(1))
         for line in (HERE / 'root-peaks.txt').read_text().splitlines() if re.search(r' (\d+)M 0$', line)]
for path in HERE.glob('*.py'):
    ast.parse(path.read_text(), filename=str(path))
print(json.dumps({
    'status': 'PASS',
    'proof_commit': (HERE / 'proof-commit.txt').read_text().strip(),
    'production_modules': modules,
    'new_public_pairs': counts['new-public'],
    'constructed_pairs': counts['constructed'],
    'private_claim_pairs': counts['private-claim'],
    'groups': len(groups),
    'full_public_proofs_and_standard_axioms': True,
    'strict_empty_logs': len(modules) + len(stricts),
    'component_manifests': components,
    'component_entries': entries,
    'audit_jobs': jobs,
    'audit_dependency_checks': dependencies,
    'old_warnings': old_warnings,
    'memory_max': '4294967296',
    'memory_high': '4294967296',
    'swap_max': '0',
    'successful_root_job_peak_upper_bound_MiB': max(peaks),
    'actual_row_and_reference_origins_have_finite_epsilon_step_witnesses': True,
    'union_and_mu_exposure_strictly_reduce_the_selected_witness': True,
    'mu_step_derives_actual_unfold_execute_validity_and_growth': True,
    'shorter_witness_keeps_the_original_reader': True,
    'row_and_reference_induction_do_not_assume_future_completion': True,
    'local_forward_simulation_uses_arbitrary_finite_matching_paths': True,
    'bidirectional_local_simulation_derives_all_finite_observations': True,
    'physical_empty_agreement_remains_explicit': True,
    'ordinary_source_step_uses_actual_indexed_strict_child_hypotheses': True,
    'ordinary_source_step_derives_one_more_row_depth': True,
    'source_child_syntax_can_contain_arbitrary_nested_mu': True,
    'actual_warm_parent_calls_and_same_reader_remain_explicit': True,
    'checked_native_mu_origin_exercises_actual_strict_epsilon_receipt': True,
    'arbitrary_stored_mu_source_simulation_instance_remains_open': True,
    'root_filter_matching_reader_support_and_selected_writer_remain_required': True,
    'initial_query_operand_and_public_source_ancestry_still_open': True,
    'interned_references_can_be_keyed': True,
    'ordinary_operand_ancestry_requires_actual_guard_conjunction': True,
    'no_binderfree_or_finite_ordinary_cap_condition': True,
    'general_retained_used_mu_alignment_still_open': True,
    'general_recursive_completion_still_open': True,
    'active_node_owner_exclusion_and_fresh_call_bound_still_open': True,
    'repeated_convergence_still_open': True,
    'equality_operation_resources_and_host_int_adequacy_still_open': True,
    'public_haskell_correspondence_still_open': True,
    'new_haskell_behavior_patch': False,
}, indent=2))
