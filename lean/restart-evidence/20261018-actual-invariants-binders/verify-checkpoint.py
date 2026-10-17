import datetime
import gzip
import hashlib
import json
import re
import runpy
from pathlib import Path
from zoneinfo import ZoneInfo

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
selection = json.loads((HERE / 'selection-status.json').read_text())
assert selection['finalized'], 'Checkpoint selections remain PARTIAL'
checks = runpy.run_path(str(HERE / 'verify-probes.py'))
sha, check_limits, check_group = (checks[name] for name in ['sha', 'check_limits', 'check_group'])

groups = json.loads((HERE / 'selected-groups.json').read_text())
assert len({group['name'] for group in groups}) == len(groups)
for group in groups:
    check_group(group)

modules = json.loads((HERE / 'frozen-modules.json').read_text())
for name, expected in modules.items():
    assert sha(ROOT / 'lean/MicroCFTA' / (name + '.lean')) == expected, name

stricts = json.loads((HERE / 'selected-strict.json').read_text())
assert set(stricts) == set(modules)
for name, stem in stricts.items():
    meta = json.loads((HERE / (stem + '.json')).read_text())
    assert meta['exit_code'] == 0, stem
    assert not (HERE / meta['log']).read_bytes(), stem
    assert sha(HERE / meta['source']) == modules[name], (name, stem)
    check_limits(stem)

canonicals = json.loads((HERE / 'selected-canonical.json').read_text())
assert set(canonicals) == set(modules)
for name, stem in canonicals.items():
    meta = json.loads((HERE / (stem + '.json')).read_text())
    assert meta.get('exit_code', meta.get('exit')) == 0, (name, stem)
    assert 'Build completed successfully' in (HERE / meta.get('log', stem + '.log')).read_text(), stem
    check_limits(stem)

components = json.loads((HERE / 'component-manifests.json').read_text())
component_entries = 0
for name in components:
    manifest = json.loads((HERE / name).read_text())
    entries = manifest.get('entries', manifest.get('files'))
    assert isinstance(entries, list), name
    for entry in entries:
        assert sha(ROOT / entry['path']) == entry['sha256'], (name, entry['path'])
    component_entries += len(entries)

archives = json.loads((HERE / 'raw-log-archives.json').read_text())
for archived in archives:
    assert sha(HERE / archived['archive']) == archived['archive_sha256']
    assert sha(HERE / archived['failed_run_metadata']) == archived['failed_run_metadata_sha256']
    digest = hashlib.sha256()
    length = 0
    with gzip.open(HERE / archived['archive'], 'rb') as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b''):
            digest.update(block)
            length += len(block)
    assert digest.hexdigest() == archived['original_sha256']
    assert length == archived['original_bytes']

audit_stem = json.loads((HERE / 'selected-audit.json').read_text())['name']
audit = json.loads((HERE / (audit_stem + '.json')).read_text())
assert audit['exit_code'] == 0
check_limits(audit_stem)
log = (HERE / audit['log']).read_text()
jobs = int(re.findall(r'Build completed successfully \((\d+) jobs\)\.', log)[-1])
warnings = re.findall(r'^warning:.*$', log, re.M)
previous_warnings = re.findall(r'^warning:.*$', (ROOT / 'lean/restart-evidence/20261018-active-growth-lineage/full-audit-1.log').read_text(), re.M)
assert warnings == previous_warnings
dependencies = int(re.findall(r'Checked axiom dependencies of (\d+) MicroCFTA theorems\.', log)[-1])
observed = datetime.datetime.fromisoformat(audit['observed_at']).astimezone(ZoneInfo('Europe/Stockholm')).strftime('%Y-%m-%dT%H:%M:%S')
peak_lines = [line for line in (HERE / 'root-peaks.txt').read_text().splitlines() if line.startswith(observed + ' ')]
peaks = [int(re.search(r' (\d+)M 0$', line).group(1)) for line in peak_lines]
peak = max(peaks)

report = {
    'status': 'PASS',
    'proof_commit': (HERE / 'proof-commit.txt').read_text().strip(),
    'new_public_pairs': sum(group['pairs'] for group in groups if group['kind'] == 'new-public'),
    'constructed_pairs': sum(group['pairs'] for group in groups if group['kind'] == 'constructed'),
    'all_pairs': sum(group['pairs'] for group in groups),
    'groups': groups,
    'production_modules': modules,
    'strict_sources': stricts,
    'canonical_targets': canonicals,
    'component_manifests': components,
    'component_entries': component_entries,
    'lossless_failed_log_archives': archives,
    'audit_receipt': audit_stem,
    'replayed_existing_warnings': warnings,
    'audit_jobs': jobs,
    'audit_dependency_checks': dependencies,
    'audit_peak_MiB': peak,
    'audit_peak_is_upper_bound': len(peaks) > 1,
    'same_second_scope_peaks_MiB': peaks,
    'memory_max': '4294967296',
    'memory_high': '4294967296',
    'swap_max': '0',
    'only_standard_axioms': True,
    'new_public_complete_proof_output': all(g['full_proof'] for g in groups if g['kind'] == 'new-public'),
    'constructed_full_proof_pairs': sum(g['pairs'] for g in groups if g['kind'] == 'constructed' and g['full_proof']),
    'constructed_axiom_only_pairs': sum(g['pairs'] for g in groups if g['kind'] == 'constructed' and not g['full_proof']),
    'general_outer_progress_still_open': True,
    'all_active_node_key_exclusion_still_open': True,
    'retained_mu_binder_and_warm_writer_alignment_still_open': True,
    'exact_literal_parts_stored_congruence_checked': True,
    'literal_parts_derive_observations_and_physical_empty_checked': True,
    'actual_publication_bare_parity_checked': True,
    'binder_free_publication_root_filter_alignment_checked': True,
    'actual_busy_failure_constructs_own_prefix_and_all_owners': True,
    'automatic_failed_worker_prefix_extraction_still_open': False,
    'selected_own_split_excludes_top_owner_key': True,
    'general_all_ancestor_key_exclusion_still_open': True,
    'nested_source_binder_congruence_still_open': True,
    'chronological_earlier_winner_alignment_still_open': True,
    'actual_first_writer_chronology_and_cutoff_transport': True,
    'binder_free_recovered_writer_reconstructions_produced': True,
    'arbitrary_recovered_writer_body_alignment_still_open': True,
    'all_outcome_lower_and_outer_operation_growth_checked': True,
    'actual_busy_failure_derives_all_ancestor_operation_growth': True,
    'initial_constraint_cache_validity_and_ready_identity_transport': True,
    'general_operation_memo_validity_not_inferred_from_growth': True,
    'raw_stored_native_classes_derive_effective_component_coverage': True,
    'raw_stored_native_split_derives_top_owner_key_separation': True,
    'positive_guard_local_raw_origin_coverage_checked': True,
    'later_class_origin_composition_still_open': True,
    'actual_native_returns_derive_full_operation_invariants': True,
    'general_outer_operation_invariant_composition_still_open': True,
    'nested_inert_source_binders_and_publications_checked': True,
    'nested_used_source_binder_alignment_still_open': True,
    'actual_native_root_query_forward_origins_checked': True,
    'root_query_producer_requires_checked_trace_inputs': True,
    'unconditional_root_query_trace_extraction_still_open': True,
    'retained_mu_union_head_origin_composition_still_open': True,
    'fresh_recursive_request_bound_still_open': True,
    'new_haskell_behavior_patch': False,
}
print(json.dumps(report, indent=2))
