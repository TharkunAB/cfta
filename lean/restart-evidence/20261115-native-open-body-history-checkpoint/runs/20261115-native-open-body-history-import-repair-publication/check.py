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




commands = [('public-build', 'exec lake build', 0), ('strict-changed-modules', 'exec python3 /home/tritlo/Code/mcfta/lean/restart-evidence/20261115-native-open-body-history-import-repair-publication/strict-modules.py', 0), ('independent-imports', 'exec lake env lean -j1 -DwarningAsError=true /home/tritlo/Code/mcfta/lean/restart-evidence/20261115-native-open-body-history-import-repair-publication/IndependentProbes.lean', 10), ('audit-build', 'exec lake build MicroCFTA.Audit', 0), ('audit-strict', 'exec lake env lean -j1 -DwarningAsError=true MicroCFTA/Audit.lean', 336)]
for name,command,count in commands:
    run(name,command,count)
match=re.search(r'Checked axiom dependencies of (\d+) MicroCFTA theorems\.',(runtime/'audit-strict.txt').read_text())
assert match
assert checks[-1]["total_axiom_reports"] == 336
report = {'actual_prefix_remaining_inputs_proved': True, 'actual_all_source_body_returned_preservation_proved': True, 'actual_closed_self_raw_body_result_proved': True, 'actual_mismatch_raw_body_result_and_endpoint_proved': True, 'global_self_mismatch_query_laws_proved': True, 'global_self_mismatch_actual_initialization_proved': True, 'global_literal_pure_query_history_proved': True, 'source_terminal_cutoffs_from_pure_history_proved': True, 'actual_source_operation_prefix_proved': True, 'source_scoped_query_induction_proved': True, 'global_matching_top_row_history_proved': True, 'source_diagonal_row_prescribed_inputs_proved': True, 'source_diagonal_initialized_row_readback_proved': True, 'source_qualified_full_C_M_history_proved': False, 'nonterminal_auxiliary_replay_proved': False, 'raw_mu_cutoff_replay_proved': True, 'source_body_first_actual_mu_cutoff_proved': True, 'global_nonterminal_mu_cutoff_history_proved': True, 'source_initialized_mu_cutoff_composition_proved': True, 'raw_reference_replay_proved': True, 'source_body_first_reference_read_proved': True, 'global_body_first_reference_cutoff_history_proved': True, 'source_initialized_reference_cutoff_composition_proved': True, 'global_nonterminal_matching_top_row_history_proved': True, 'source_body_first_nonterminal_row_inputs_proved': True, 'source_diagonal_first_actual_body_reference_read_proved': True, 'source_initialized_nonterminal_row_composition_proved': True, 'raw_right_mu_unused_predicate_replay_proved': True, 'source_diagonal_same_key_row_inputs_proved': True, 'raw_open_body_product_original_prefix_proved': True, 'global_open_body_node_shape_history_proved': True, 'source_diagonal_actual_mu_body_branches_proved': True, 'source_initialized_diagonal_open_body_history_proved': True, 'global_open_body_right_mu_history_proved': True, 'source_initialized_diagonal_open_body_mu_history_proved': True, 'raw_reference_predicate_replay_proved': True, 'source_diagonal_same_key_reference_read_proved': True, 'all_actual_producer_families_proved': False, 'whole_native_history_returned_footprint_proved': False, 'whole_source_task_induction_proved': False, 'all_same_branch_removed_history_extracted': False, 'whole_output_satisfies_proved': False, 'joint_finite_completion_proved': False, 'compiled_haskell_correspondence_proved': False, 'haskell_changed': False}
report.update({"individual_reports":336,"source_pins_unchanged":True,"at":datetime.datetime.now().astimezone().isoformat(),"limits":limits,"checks":checks,"audited_theorems":int(match.group(1))})
(runtime/"checked.json").write_text(json.dumps(report,indent=2)+"\n")
print(json.dumps(report),flush=True)
