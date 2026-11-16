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
    item = {'name': name, 'exit': result.returncode, 'axiom_groups': len(groups), 'axiom_free_reports': free_reports, 'total_axiom_reports': len(groups) + free_reports, 'nonstandard_axioms': bad}
    checks.append(item)
    (runtime / 'checks.json').write_text(json.dumps(checks, indent=2) + '\n')
    print(json.dumps(item), flush=True)
    verify_pins()
    assert result.returncode == 0 and not bad and len(groups) + free_reports >= required_groups
    assert 'sorryAx' not in output




jobs = [('public-build', 'exec lake build', 0), ('strict-modules-136-resources-and-held-history', 'exec python3 /home/tritlo/Code/mcfta/lean/restart-evidence/20261116-residual-finalize-history-publication/strict-modules.py', 143), ('independent-imports', 'exec lake env lean -j1 -DwarningAsError=true /home/tritlo/Code/mcfta/lean/restart-evidence/20261116-residual-finalize-history-publication/IndependentProbes.lean', 111), ('audit-build', 'exec lake build MicroCFTA.Audit', 0), ('audit-strict', 'exec lake env lean -j1 -DwarningAsError=true MicroCFTA/Audit.lean', 516)]
for name,command,count in jobs:
    run(name,command,count)
match = re.search(r'Checked axiom dependencies of (\d+) MicroCFTA theorems\.',(runtime/'audit-strict.txt').read_text())
assert match and checks[-1]['total_axiom_reports'] == 516
report = {'checks':checks,'source_pins_unchanged':True,'audited_theorems':int(match.group(1)),
    'individual_reports':516,'owner_resource_probes':143,'original_resource_probes':136,'private_local_finalize_probes':2,'private_source_qualification_and_callback_probes':5,'total_private_resource_probes':7,'independent_reports':111,
    'identity_worker_emitted_resources_at_any_budget_proved':True,
    'whole_real_worker_at_any_budget_proved':True,'real_task_induction_under_genuine_depth_ih_proved':True,'actual_captured_startup_and_opaque_proved':True,
    'original_real_public_header':'549358aad6c1d3c04f55dbff2a5ab2a9cc61863082c0d955adbb0f293520b607',
    'actual_same_key_past_payload_proved':True,'generic_runtime_equations_proved':8,
    'joint_finite_completion_proved':False,'whole_warm_source_history_proved':False,'next_actual_query_inner_laws_from_past_producers_proved':True,'actual_selected_prefix_union_normal_proved':True,'full_worker_union_normal_proved':True,'full_worker_none_buckets_proved':True,'actual_configured_cps_and_height_proved':True,'actual_source_done_rendering_proved':True,'actual_pending_rendering_assignment_proved':True,'actual_empty_root_singleton_parent_proved':True,'actual_source_enter_closed_operands_proved':True,'actual_source_current_assignment_factory_proved':True,'actual_child_none_buckets_proved':True,'actual_issued_domain_origin_proved':True,'actual_eager_parked_receipt_proved':True,'actual_canonical_old_entry_proved':True,'retained_core_obligations_guardsHold_proved':False,'actual_source_current_rendered_satisfies_with_checked_residuals_proved':True,'source_pending_boundary_atom_OnlyU_is_explicit':True,'source_pending_Profile_closure_proved':False,'source_factory_None_supplier_removed':True,'actual_warm_entry_and_return_admission_proved':True,'actual_warm_node_and_edge_return_admission_proved':True,'actual_prepared_parent_path_congruence_proved':True,'actual_prepared_incoming_query_history_proved':True,'private_tuple_finalize_pending_target_avoidance_proved':True,'full_worker_906_avoidance_proved':False,'residual_finalize_commutation_at_same_budget_proved':True,'held_history_after_residual_proved':True,'past_to_actual_performed_phase_history_proved':True,'concrete_held_fragment_receipt_composition_proved':True,'concrete_held_fragment_pending_target_projection_proved':True,'private_tuple_finalize_held_history_proved':True,'private_actual_captured_pending_at_rowOwn_proved':True,'private_captured_boundary_separation_proved':True,'private_actual_callback_held_history_with_genuine_depth_IH_proved':True,'original_budget_admitted_physical_and_field_plans_proved':True,'one_removed_arrow_bucket_same_assignment_proved':True,'all_removed_history_joint_proved':False,'actual_none_cached_writers_proved':True,'actual_selected_preparation_union_normal_proved':True,'actual_shared_dispatch_union_normal_proved':True,'actual_shared_terminal_union_normal_proved':True,'actual_shared_child_union_normal_proved':True,'actual_cold_cell_past_gamma_transport_proved':True,'current_pending_assignment_proved':True,
    'compiled_haskell_correspondence_proved':False,'haskell_changed':False,
    'at':datetime.datetime.now().astimezone().isoformat(),'limits':limits}
(runtime/'checked.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report),flush=True)
