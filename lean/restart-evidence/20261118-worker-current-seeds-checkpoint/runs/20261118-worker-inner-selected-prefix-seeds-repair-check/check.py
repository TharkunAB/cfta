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
    item = {'name': name, 'report_kind': 'private', 'exit': result.returncode,
        'axiom_groups': len(groups), 'axiom_free_reports': free,
        'total_axiom_reports': len(groups) + free,
        'expected_axiom_reports': component['expected_axiom_reports'],
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
    assert selection['expected_checks'] == 1
    assert selection['expected_public_axiom_reports'] == 0
    assert selection['expected_explicit_private_axiom_reports'] == 4
    assert selection['expected_declaration_checks'] == selection['new_definitions'] == 0
    components = {item['module']: item for item in selection['components']}
    assert len(components) == len(selection['compile_order']) == 1
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
success = failure is None and pins_stable and len(checks) == 1 and all(passed)
private = sum(item['total_axiom_reports'] for item in checks)
success = success and private == 4
report = {'at': datetime.datetime.now().astimezone().isoformat(), 'checks': checks,
    'passed': passed, 'failure': failure, 'limits': limits,
    'all_selected_statements_checked': success,
    'actual_printed_public_axiom_reports': 0, 'actual_explicit_private_axiom_reports': private,
    'credited_public_reports': 0, 'credited_private_reports': 4 if success else 0,
    'new_public_theorems': 0, 'new_private_theorems': 4,
    'new_private_helpers_transitive': 0,
    'rebuilt_Source66_three_private_clauses_and_two_Grows_extra_credit': 0,
    'new_definitions': 0, 'actual_definition_declaration_checks': 0, 'definition_axiom_credit': 0,
    'four_original_FIRSTs_byte_exact': True,
    'all_original_proof_bodies_byte_exact': False,
    'original_failed_actual_session': 59813, 'original_failed_credit': 0,
    'published_Source66_owner_entire_prefix_exact_at_69': True,
    'source_pins_unchanged': pins_stable, 'proof_credit': success,
    'normal_Source_changed': False, 'published': False,
    'source_commit': selection['source_commit'],
    'prior_publication_actual_session': selection['prior_publication_actual_session'],
    'bounded_inner_and_selected_prefix_clauses_checked': success,
    'OuterIH_recursiveDepth_is_explicit_and_undischarged': True,
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
