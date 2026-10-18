import datetime
import json
import re
import runpy
from pathlib import Path
from zoneinfo import ZoneInfo

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]


def read(name):
    return json.loads((HERE / name).read_text())


checks = runpy.run_path(str(HERE / 'verify-probes.py'))
assert read('selection-status.json')['finalized']
groups = read('selected-groups.json')
assert len({group['name'] for group in groups}) == len(groups)
public = sum(group['pairs'] for group in groups if group['kind'] == 'new-public')
constructed = sum(group['pairs'] for group in groups if group['kind'] == 'constructed')
assert public == 12
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
old_log = (ROOT / 'lean/restart-evidence/20261018-selected-read-producers/full-audit-1.log').read_text()
old_warnings = re.findall(r'^warning:.*$', old_log, re.M)
for module, stem in read('selected-canonical.json').items():
    receipt = read(stem + '.json')
    log = (HERE / receipt['log']).read_text()
    assert receipt['exit_code'] == 0 and 'Build completed successfully' in log
    assert re.findall(r'^warning:.*$', log, re.M) == old_warnings
    checks['check_limits'](stem)
stricts = read('selected-constructed-strict.json')
assert len(stricts) == 2
for stem in stricts:
    receipt = read(stem + '.json')
    assert receipt['exit_code'] == 0 and not (HERE / receipt['log']).read_bytes()
    checks['check_limits'](stem)
components = read('component-manifests.json')
assert len(components) == 6
entries = 0
for name in components:
    for entry in read(name)['entries']:
        path = ROOT / entry['path']
        assert checks['sha'](path) == entry['sha256'], (name, entry['path'])
        if 'bytes' in entry:
            assert path.stat().st_size == entry['bytes']
        entries += 1
receipt = read('full-audit-1.json')
assert receipt['exit_code'] == 0
checks['check_limits']('full-audit-1')
log = (HERE / receipt['log']).read_text()
warnings = re.findall(r'^warning:.*$', log, re.M)
assert warnings == old_warnings
jobs = int(re.findall(r'Build completed successfully \((\d+) jobs\)\.', log)[-1])
dependencies = int(re.findall(r'Checked axiom dependencies of (\d+) MicroCFTA theorems\.', log)[-1])
assert jobs == 3237 and dependencies == 70923
observed = datetime.datetime.fromisoformat(receipt['observed_at']).astimezone(
    ZoneInfo('Europe/Stockholm')).strftime('%Y-%m-%dT%H:%M:%S')
peaks = [int(re.search(r' (\d+)M 0$', line).group(1))
         for line in (HERE / 'root-peaks.txt').read_text().splitlines()
         if line.startswith(observed + ' ')]
assert peaks
print(json.dumps({
    'status': 'PASS',
    'proof_commit': (HERE / 'proof-commit.txt').read_text().strip(),
    'production_modules': modules,
    'new_public_pairs': public,
    'constructed_pairs': constructed,
    'groups': len(groups),
    'full_public_proofs_and_standard_axioms': True,
    'strict_empty_logs': len(modules) + len(stricts),
    'component_manifests': components,
    'component_entries': entries,
    'audit_jobs': jobs,
    'audit_dependency_checks': dependencies,
    'old_warnings': warnings,
    'memory_max': '4294967296',
    'memory_high': '4294967296',
    'swap_max': '0',
    'audit_peak_MiB': max(peaks),
    'initial_flat_physical_guard_bounds_computed': True,
    'resident_live_precheck_class_path_and_step_bounds_constructed': True,
    'native_guard_limits_follow_literal_finite_alphabet_extensions': True,
    'initial_native_query_constructs_receipt_and_returned_guard_bounds': True,
    'single_parent_reservation_derived_from_exact_initial_finite_alphabet': True,
    'compiled_index_sizes_retained_by_exact_own_record_image': True,
    'no_inherited_size_cap_or_finite_ordinary_domain_added': True,
    'no_future_entry_capacity_callback_or_success_premise_added': True,
    'initial_semantic_context_and_resource_limits_remain_explicit': True,
    'general_bounded_outer_numeric_schedule_still_open': True,
    'general_outer_prefix_semantic_context_transport_still_open': True,
    'general_recursive_outer_completion_still_open': True,
    'all_active_key_exclusion_still_open': True,
    'finite_fresh_call_bound_still_open': True,
    'recursive_outer_language_preservation_still_open': True,
    'used_binder_and_earlier_writer_alignment_still_open': True,
    'repeated_convergence_still_open': True,
    'public_haskell_correspondence_still_open': True,
    'new_haskell_behavior_patch': False,
}, indent=2))
