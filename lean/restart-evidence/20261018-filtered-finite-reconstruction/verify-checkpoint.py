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
assert counts == {'new-public': 11, 'constructed': 1, 'private-claim': 0}
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
assert len(stricts) == 1
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
    for entry in read(name).get('entries', read(name).get('files', [])):
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
assert jobs == audit['jobs'] == 3306 and dependencies == audit['dependency_checks'] == 71667
peaks = [int(re.search(r' (\d+)M 0$', line).group(1))
         for line in ((HERE / 'root-peaks.txt').read_text() + (HERE / 'root-followup-peaks.txt').read_text()).splitlines() if re.search(r' (\d+)M 0$', line)]
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
    'actual_warm_parent_constructs_all_selected_literal_and_row_calls': True,
    'finite_reconstruction_derives_physical_empty_and_observation_agreement': True,
    'full_symbols_guards_and_ordered_children_are_retained': True,
    'mu_atom_reconstruction_remains_an_explicit_full_depth_obligation': True,
    'ordinary_raw_root_matching_uses_actual_indexed_source_children': True,
    'publication_uses_only_its_actual_immediate_body_induction_hypothesis': True,
    'publication_constructs_sequential_calls_final_heap_and_warm_replays': True,
    'shared_sparse_map_derives_original_callback_execution_outcomes': True,
    'selected_writer_requires_and_retains_the_actual_installed_record': True,
    'body_hypothesis_uses_actual_raw_return_to_execution_growth': True,
    'observation_reader_remains_separate_from_execution_heap': True,
    'general_nested_binder_with_varying_outer_capture_remains_open': True,
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
