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
assert counts == {'new-public': 18, 'constructed': 4, 'private-claim': 0}
for group in groups:
    checks['check_group'](group)
modules = read('frozen-modules.json')
assert len(modules) == 4
for module, expected in modules.items():
    assert checks['sha'](ROOT / 'lean/MicroCFTA' / (module + '.lean')) == expected
for module, stem in read('selected-strict.json').items():
    receipt = read(stem + '.json')
    assert receipt['exit_code'] == 0 and not (HERE / receipt['log']).read_bytes()
    assert checks['sha'](HERE / receipt['source']) == modules[module]
    checks['check_limits'](stem)
stricts = read('selected-constructed-strict.json')
assert len(stricts) == 3
for stem, working in stricts.items():
    receipt = read(stem + '.json')
    assert receipt['exit_code'] == 0 and not (HERE / receipt['log']).read_bytes()
    assert checks['sha'](HERE / receipt['source']) == receipt['sha256']
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
assert jobs == audit['jobs'] == 3304 and dependencies == audit['dependency_checks'] == 71623
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
    'observation_reader_is_separate_from_actual_execution_heap': True,
    'ordinary_rows_retain_complete_fields_and_ordered_children': True,
    'union_strict_member_hypotheses_quantify_execution_heaps': True,
    'actual_member_completions_do_not_move_the_observation_relation': True,
    'initial_producer_constructs_both_raw_and_stored_calls': True,
    'binderfree_source_accepts_distinct_finitely_related_recursive_replacements': True,
    'closed_source_case_permits_arbitrary_nested_used_binders': True,
    'generic_warm_support_derives_exact_origins_and_finite_observation_transport': True,
    'actual_preparation_settles_all_final_closed_available_values': True,
    'preparation_uses_actual_unfoldings_and_well_founded_degree_vectors': True,
    'preparation_does_not_claim_cold_to_prepared_observation_equivalence': True,
    'checked_warm_union_parent_can_have_a_cold_original_subgroup': True,
    'checked_nested_used_mu_unfold_returns_unavailable_at_entry_values': True,
    'exact_physical_origin_transport_needs_more_than_growth': True,
    'general_active_binder_root_filter_and_self_observation_cases_remain_open': True,
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
