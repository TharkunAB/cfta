from pathlib import Path
import datetime
import hashlib
import json
import os
import re
import shlex
import subprocess

root = Path('/home/tritlo/Code/mcfta')
runtime = Path(__file__).resolve().parent
selection = json.loads((runtime / 'selection.json').read_text())
pins = json.loads((runtime / 'source-pins.json').read_text())
checks = []
limits = {}
failure = None
pins_stable = False


def verify_pins():
    for name, digest in pins.items():
        assert hashlib.sha256((root / name).read_bytes()).hexdigest() == digest, name


def run(component):
    verify_pins()
    name = component['module']
    (runtime / 'running.json').write_text(json.dumps({
        'name': name, 'at': datetime.datetime.now().astimezone().isoformat(),
    }) + '\n')
    command = 'exec lake env python3 ' + shlex.quote(str(runtime / 'shadow-compile.py'))
    command += ' ' + shlex.quote(name)
    environment = dict(os.environ)
    environment.pop('LEAN_SYSROOT', None)
    environment['LEAN_NUM_THREADS'] = '1'
    path = runtime / (name + '.txt')
    with path.open('w') as log:
        result = subprocess.run(['nix-shell', str(root / 'shell.nix'), '--run', command],
            cwd=root / 'lean', env=environment, stdout=log, stderr=subprocess.STDOUT, text=True)
    output = path.read_text()
    groups = [set(item.strip() for item in group.split(',') if item.strip())
        for group in re.findall(r'depends on axioms:\s*\[([^]]*)\]', output, re.S)]
    free = len(re.findall(r'does not depend on any axioms', output))
    bad = sorted(set().union(*groups) - {'propext', 'Classical.choice', 'Quot.sound'}) if groups else []
    definition_prefix = r'(?:_private\.MicroCFTA\.SourcePruningEnumerationSharedEagerReservation\.\d+\.)?'
    definition_counts = {
        qname: len(re.findall(r'^' + definition_prefix + re.escape(qname)
            + r'(?=\s|\.?\{|\(|:)', output, re.M))
        for qname in component['definition_qnames']}
    declarations = sum(definition_counts.values())
    item = {'name': name, 'exit': result.returncode, 'axiom_groups': len(groups),
        'axiom_free_reports': free, 'total_axiom_reports': len(groups) + free,
        'expected_axiom_reports': component['expected_axiom_reports'],
        'declaration_checks': declarations, 'definition_checks_by_qname': definition_counts,
        'nonstandard_axioms': bad, 'diagnostics': len(re.findall(r': error(?:\(|:)', output)),
        'sorryAx': 'sorryAx' in output}
    checks.append(item)
    (runtime / 'checks.json').write_text(json.dumps(checks, indent=2) + '\n')
    print(json.dumps(item), flush=True)
    verify_pins()


try:
    assert not (runtime / 'checked.json').exists()
    group = next(line.split(':', 2)[2] for line in Path('/proc/self/cgroup').read_text().splitlines()
        if line.startswith('0::'))
    cgroup = Path('/sys/fs/cgroup') / group.lstrip('/')
    limits = {name: (cgroup / name).read_text().strip()
        for name in ['memory.max', 'memory.high', 'memory.swap.max']}
    assert limits == {'memory.max': '8589934592', 'memory.high': '8589934592', 'memory.swap.max': '0'}
    assert selection['expected_checks'] == 1
    assert selection['expected_public_axiom_reports'] == 0
    assert selection['expected_explicit_private_axiom_reports'] == 1
    assert selection['expected_declaration_checks'] == 3
    run(selection['components'][0])
    verify_pins()
    pins_stable = True
except Exception as error:
    failure = {'type': type(error).__name__, 'message': str(error)}
passed = [item['exit'] == 0 and not item['diagnostics'] and not item['sorryAx']
    and not item['nonstandard_axioms'] and item['declaration_checks'] == 3
    and len(item['definition_checks_by_qname']) == 3
    and all(count == 1 for count in item['definition_checks_by_qname'].values())
    and item['total_axiom_reports'] == item['expected_axiom_reports'] == 1 for item in checks]
success = failure is None and pins_stable and len(checks) == 1 and all(passed)
report = {'at': datetime.datetime.now().astimezone().isoformat(), 'checks': checks,
    'passed': passed, 'failure': failure, 'limits': limits,
    'single_component_checked': success, 'all_selected_statements_checked': success,
    'corrected_base_FIRST_bound_and_original_three_motives_exact': True,
    'actual_printed_public_axiom_reports': 0,
    'credited_public_reports': 0,
    'actual_outer_depth_zero_endpoint_seeds_base_checked': success,
    'actual_explicit_private_axiom_reports': sum(item['total_axiom_reports'] for item in checks),
    'credited_private_reports': 1 if success else 0, 'actual_definition_declaration_checks': sum(item['declaration_checks'] for item in checks),
    'new_private_helpers_transitive': 0, 'new_private_theorems': 1, 'new_definitions': 3, 'new_private_Prop_definitions': 3, 'definition_axiom_credit': 0,
    'all_original_FIRST_header_bytes_exact': False,
    'FIRST_bytes_changed': True,
    'original_FIRST_successfully_elaborated': False,
    'corrected_FIRST_explicit_width_insertion_bytes': 15,
    'proof_and_three_motives_byte_exact': True,
    'first_failed_actual_session': 78387, 'first_failed_credit': 0,
    'fresh_credit_for_old_owner_theorems': 0,
    'source_pins_unchanged': pins_stable, 'proof_credit': success,
    'normal_Source_changed': False, 'published': False,
    'source_commit': selection['source_commit'],
    'prior_publication_actual_session': selection['prior_publication_actual_session'],
    'outer_recursive_depth_zero_only': True,
    'all_literal_decisions_and_outputs_at_depth_zero': True,
    'rebuilt_prior_leaf_extra_credit': 0,
    'genuine_past_source_Seeds_and_Grows_required': True,
    'old_owner_entire_contiguous_block_exact': True,
    'verified_Source64_prefix_entire_byte_exact': True,
    'complete_eager_worker_query_log_proved': False,
    'all_original_supplied_fuels_and_endpoints_retained': True,
    'proof_limits': 'default proof limits; no override',
    'cache_data_copied': False,
    'prior_checkpoint_push_required_before_normal_Source_staging': True,
    'all_original_eager_worker_query_admissions_proved': False,
    'original_eager_worker_all_calls_Seeds_propagation_proved': False,
    'native_inhabitance_proved': False, 'guard_truth_proved': False,
    'joint_finite_completion_proved': False, 'haskell_changed': False}
(runtime / 'results.json').write_text(json.dumps(report, indent=2) + '\n')
if not success:
    print(json.dumps(report), flush=True)
    raise SystemExit(1)
(runtime / 'checked.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report), flush=True)
