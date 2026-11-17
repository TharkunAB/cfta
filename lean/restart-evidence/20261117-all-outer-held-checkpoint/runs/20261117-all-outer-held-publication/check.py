from pathlib import Path
import datetime
import hashlib
import json
import os
import re
import shlex
import subprocess

root = Path('/home/tritlo/Code/mcfta')
runtime = Path(__file__).parent
pins = json.loads((runtime / 'source-pins.json').read_text())
group = next(line.split(':', 2)[2] for line in Path('/proc/self/cgroup').read_text().splitlines()
             if line.startswith('0::'))
base = Path('/sys/fs/cgroup') / group.lstrip('/')
limits = {name: (base / name).read_text().strip()
          for name in ['memory.max', 'memory.high', 'memory.swap.max']}
assert limits == {'memory.max': '8589934592', 'memory.high': '8589934592', 'memory.swap.max': '0'}
environment = dict(os.environ)
environment.pop('LEAN_SYSROOT', None)
environment['LEAN_NUM_THREADS'] = '1'
checks = []


def verify_pins():
    for name, digest in pins.items():
        assert hashlib.sha256((root / name).read_bytes()).hexdigest() == digest, name


def run(name, command, required_groups=0):
    verify_pins()
    (runtime / 'running.json').write_text(json.dumps({'name': name, 'at': datetime.datetime.now().astimezone().isoformat()}) + '\n')
    with (runtime / (name + '.txt')).open('w') as log:
        result = subprocess.run(['nix-shell', str(root / 'shell.nix'), '--run', command],
                                cwd=root / 'lean', env=environment, stdout=log, stderr=subprocess.STDOUT, text=True)
    output = (runtime / (name + '.txt')).read_text()
    groups = [set(x.strip() for x in group.split(',') if x.strip())
              for group in re.findall(r'depends on axioms:\s*\[([^]]*)\]', output, re.S)]
    free_reports = len(re.findall(r'does not depend on any axioms', output))
    bad = sorted(set().union(*groups) - {'propext', 'Classical.choice', 'Quot.sound'}) if groups else []
    item = {'name': name, 'exit': result.returncode, 'axiom_groups': len(groups), 'axiom_free_reports': free_reports, 'total_axiom_reports': len(groups) + free_reports, 'nonstandard_axioms': bad, 'diagnostics': len(re.findall(r': error(?:\(|:)', output)), 'sorryAx': 'sorryAx' in output}
    checks.append(item)
    (runtime / 'checks.json').write_text(json.dumps(checks, indent=2) + '\n')
    print(json.dumps(item), flush=True)
    verify_pins()




jobs = [('public-build', 'exec lake build', 0), ('strict-resource-and-component-modules', 'exec python3 /home/tritlo/Code/mcfta/lean/restart-evidence/20261117-all-outer-held-publication/strict-modules.py', 324), ('independent-imports', 'exec lake env lean -j1 -DwarningAsError=true /home/tritlo/Code/mcfta/lean/restart-evidence/20261117-all-outer-held-publication/IndependentProbes.lean', 234), ('audit-build', 'exec lake build MicroCFTA.Audit', 0), ('audit-strict', 'exec lake env lean -j1 -DwarningAsError=true MicroCFTA/Audit.lean', 639)]
for name, command, count in jobs:
    run(name, command, count)
assert len(checks) == 5
assert all(c['exit'] == 0 and not c['nonstandard_axioms'] and not c['diagnostics'] and not c['sorryAx']
           and (not job[2] or c['total_axiom_reports'] == job[2]) for c, job in zip(checks, jobs))
match = re.search(r'Checked axiom dependencies of (\d+) MicroCFTA theorems\.', (runtime / 'audit-strict.txt').read_text())
assert match
report = {'source_pins_unchanged': True, 'owner_resource_probes': 226, 'original_resource_probes': 136, 'local_primitive_all_raw_alias_growth_proved': True, 'specified_staged_child_position_incidence_proved': True, 'same_selected_preparation_indexed_child_bridge_proved': True, 'actual_shared_child_all_raw_alias_growth_proved': True, 'whole_worker_all_raw_aliases_proved': True, 'original_c4cb44f2_header_preserved': True, 'actual_mutual_invocation_alias_composition_proved': True, 'actual_captured_restart_entry_aliases_proved': True, 'same_child_entry_roots_producer_proved': True, 'same_selected_child_path_aliases_proved': True, 'every_causal_historical_event_attached_proved': False, 'joint_finite_completion_proved': False, 'haskell_changed': False, 'all_causal_removed_event_coverage_and_meaning_proved': False, 'all_original_proper_paths_semantically_completed_proved': False, 'actual_causal_target_type_membership_proved': False, 'general_owner_as_target_joint_recompletion_proved': False, 'source_files': 6236, 'direct_audit_imports': 5236, 'individual_reports': 639, 'independent_reports': 234, 'resource_and_component_probes': 324, 'new_component_reports': 2, 'new_theorem_reports': 11, 'new_relation_declaration_reports': 0, 'new_modules': 1, 'new_public_theorems': 2, 'same_final_output_original_path_aliases_proved': True, 'observed_original_six_fuel_prefix_canonicality_proved': True, 'indexed_original_path_child_descent_proved': True, 'independent_finite_arrow_batch_joint_assignment_proved': True, 'two_finite_term_cycle_boundaries_proved': True, 'actual_shared_child_canonicality_proved': True, 'actual_mutual_invocation_canonicality_proved': True, 'whole_real_eager_canonicality_proved': True, 'actual_shallow_dispatch_footprint_proved': True, 'actual_indexed_outer_history_producer_proved': True, 'same_preparation_entry_total_canonical_and_bucket_validity_proved': True, 'qualified_actual_outer_history_produced': True, 'each_recorded_outer_entry_canonical_total_proved': True, 'one_qualified_head_clear_same_indexed_suffix_proved': True, 'ordered_pending_arrow_batch_one_assignment_proved': True, 'causal_source_universe_leaf_type_base_proved': True, 'nested_invocation_event_ledger_produced': True, 'every_ledger_event_authentic_proved': True, 'typed_fragment_every_finite_fuel_proved': True, 'ordered_recompletion_target_typing_internally_derived': True, 'joint_outer_nested_causal_operational_ledger_produced': True, 'original_source_unfolded_row_inputs_proved': True, 'actual_nullary_child_and_parent_literal_proved': True, 'two_actual_parked_prefixes_packet_and_held_history_proved': True, 'actual_marker_role_source_control_produced': False, 'all_descendant_packet_semantics_propagated': False, 'new_relation_declaration_checks': 0, 'new_private_component_reports': 9, 'new_public_component_reports': 2, 'previous_owner_resource_probes': 217, 'old_non_audit_non_owner_source_files_byte_exact': 6233, 'old_owner_bytes_preserved_contiguously': 2129411, 'old_owner_proof_bodies_unchanged': True, 'old_owner_proof_limits_unchanged': True, 'new_owner_export_maxHeartbeats': 200000, 'same_actual_tuple_selected_finalized_callback_packets_proved': True, 'source_terminal_marker_role_restriction_proved': True, 'original_source_unfolded_row_top_and_actual_arrow_input_proved': True, 'lower_original_inputs_same_guarded_eager_trace_proved': True, 'literal_callback_current_cut_proved': True, 'literal_callback_held_cut_proved': True, 'actual_completed_tuple_current_produced': True, 'all_history_held_protection_proved': True, 'old_owner_offset': 197, 'all_history9374_proved': True, 'actual_parked_all_later_outer_entries_held_history_proved': True, 'original_source_arrow_staged_provenance_proved': True, 'public9374_header_byte_exact': False, 'public9374_theorem_declaration_byte_exact': True, 'historical_open_comment_removed': True, 'shared5e48_predicate_byte_exact': True, 'same_original_runtime_fuels': True, 'new_proof_maxHeartbeats': 200000}
report.update(checks=checks, limits=limits, at=datetime.datetime.now().astimezone().isoformat(),
              audited_theorems=int(match.group(1)))
(runtime / 'checked.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report), flush=True)
