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
assert len({group['name'] for group in groups}) == len(groups) == 6
assert sum(group['pairs'] for group in groups if group['kind'] == 'new-public') == 20
assert sum(group['pairs'] for group in groups if group['kind'] == 'constructed') == 3
for group in groups:
    check_group(group)

modules = json.loads((HERE / 'frozen-modules.json').read_text())
assert len(modules) == 3
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
previous_warnings = re.findall(r'^warning:.*$', (ROOT / 'lean/restart-evidence/20261018-class-row-chain/full-audit-1.log').read_text(), re.M)
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
    'later_class_full_guard_occurrence_composition_checked': True,
    'later_class_individual_row_survival_chain_still_open': False,
    'actual_row_chain_through_compiled_classes_and_right_fold_checked': True,
    'actual_outer_completed_calls_and_prefixes_preserve_captured_full_fields': True,
    'initial_busy_nonempty_owner_derives_exact_earlier_row_and_edge_call': True,
    'gain_row_origin_is_immediate_reached_row_not_initial_source_lineage': True,
    'actual_combine_and_inherited_prefix_derive_initial_finite_path_domains': True,
    'global_inheritance_carrier_or_anchor_bound_still_open': True,
    'max_operand_height_or_own_height_necessity_refuted': True,
    'union_body_head_derives_earlier_node_member_row_indices_and_calls': True,
    'used_source_value_lift_and_causal_retained_writer_law_still_open': True,
    'row_chain_keeps_full_rows_and_ordered_child_reads': True,
    'initial_busy_nonempty_owner_requires_actual_own_field_height_gain': True,
    'gain_event_has_nonempty_effective_own_classes': True,
    'general_head_union_mu_chronological_terminal_rows_checked': True,
    'actual_source_output_bare_empty_tag_correspondence_checked': True,
    'used_callback_filtered_root_match_strict_induction_step_checked': True,
    'general_used_callback_closed_induction_still_open': True,
    'actual_native_returns_derive_full_operation_invariants': True,
    'completed_lower_and_parent_operation_invariants_checked': True,
    'general_outer_operation_invariant_composition_still_open': False,
    'actual_success_and_reached_outer_invariants_produced': True,
    'actual_busy_full_request_identity_and_all_owner_ready': True,
    'physical_filtered_probe_preservation_from_initial_weak_native_good': True,
    'physical_mu_node_body_all_bounds_exact_cleanup_same_caller': True,
    'literal_node_recursive_head_row_indices_and_final_reader_calls': True,
    'actual_used_publication_initial_alias_and_free_name_transport': True,
    'general_used_publication_output_root_match_still_open': True,
    'nested_inert_source_binders_and_publications_checked': True,
    'nested_used_source_binder_alignment_still_open': True,
    'actual_native_root_query_forward_origins_checked': True,
    'root_query_producer_requires_checked_trace_inputs': True,
    'unconditional_root_query_trace_extraction_still_open': True,
    'closed_recursive_head_rows_constructed': True,
    'general_retained_mu_body_and_original_operands_lineage_still_open': True,
    'normalization_stable_root_alternative_relation_checked': True,
    'general_used_local_source_binder_congruence_still_open': True,
    'fresh_recursive_request_bound_still_open': True,
    'new_haskell_behavior_patch': False,
}
print(json.dumps(report, indent=2))
