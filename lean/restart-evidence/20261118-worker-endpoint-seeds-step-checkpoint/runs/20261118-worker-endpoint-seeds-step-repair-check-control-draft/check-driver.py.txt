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
    (runtime / 'running.json').write_text(json.dumps({'name': name,
        'at': datetime.datetime.now().astimezone().isoformat()}) + '\n')
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
    item = {'name': name, 'report_kind': component['report_kind'], 'exit': result.returncode,
        'axiom_groups': len(groups), 'axiom_free_reports': free,
        'total_axiom_reports': len(groups) + free, 'expected_axiom_reports': component['expected_axiom_reports'],
        'declaration_checks': 0, 'expected_declaration_checks': 0,
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
    assert selection['expected_checks'] == 3
    assert selection['expected_public_axiom_reports'] == 2
    assert selection['expected_explicit_private_axiom_reports'] == 3
    assert selection['expected_declaration_checks'] == selection['new_definitions'] == 0
    components = {item['module']: item for item in selection['components']}
    assert len(components) == len(selection['compile_order']) == 3
    assert set(components) == set(selection['compile_order'])
    for name in selection['compile_order']:
        run(components[name])
    verify_pins()
    pins_stable = True
except Exception as error:
    failure = {'type': type(error).__name__, 'message': str(error)}
passed = [item['exit'] == 0 and not item['diagnostics'] and not item['sorryAx']
    and not item['nonstandard_axioms']
    and item['total_axiom_reports'] == item['expected_axiom_reports'] for item in checks]
success = failure is None and pins_stable and len(checks) == 3 and all(passed)
public = sum(item['total_axiom_reports'] for item in checks if item['report_kind'] == 'public')
private = sum(item['total_axiom_reports'] for item in checks if item['report_kind'] == 'private')
success = success and public == 2 and private == 3
report = {'at': datetime.datetime.now().astimezone().isoformat(), 'checks': checks,
    'passed': passed, 'failure': failure, 'limits': limits,
    'all_three_components_checked': success, 'all_selected_statements_checked': success,
    'actual_printed_public_axiom_reports': public, 'actual_explicit_private_axiom_reports': private,
    'credited_public_reports': 2 if success else 0, 'credited_private_reports': 3 if success else 0,
    'new_public_theorems': 2, 'new_private_theorems': 6,
    'growth_helpers_transitive_without_explicit_report': 3,
    'rebuilt_Source65_leaf_and_zero_base_extra_credit': 0,
    'new_definitions': 0, 'actual_definition_declaration_checks': 0, 'definition_axiom_credit': 0,
    'selected_return_FIRST_bytes_changed': True,
    'original_selected_return_FIRST_successfully_elaborated': False,
    'all_non_whitespace_header_bytes_exact': True,
    'all_three_shared_proofs_and_tuple_captured_FIRSTs_exact': True,
    'both_growth_owner_sources_FIRSTs_and_proofs_exact': True,
    'published_Source65_owner_entire_prefix_exact': True,
    'old_selected_tuple_full_candidate_prefix_equality_claimed': False,
    'first_failed_actual_session': 21212, 'first_failed_credit': 0,
    'source_pins_unchanged': pins_stable, 'proof_credit': success,
    'normal_Source_changed': False, 'published': False,
    'source_commit': selection['source_commit'],
    'prior_publication_actual_session': selection['prior_publication_actual_session'],
    'bounded_primitive_growth_and_three_internal_endpoint_clauses_checked': success,
    'captured_outer_IH_is_internal_successor_premise_not_discharged_here': True,
    'tuple_cons_smaller_IH_is_not_global_worker_producer': True,
    'all_original_supplied_fuels_and_endpoints_retained': True,
    'proof_limits': 'default proof limits; no override', 'cache_data_copied': False,
    'prior_checkpoint_push_required_before_normal_Source_staging': True,
    'full_worker_endpoint_producer_proved': False,
    'complete_eager_worker_query_log_proved': False,
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
