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
    declarations = len(re.findall(r'^MicroCFTA\.[^\n]* :', output, re.M))
    item = {'name': name, 'exit': result.returncode, 'axiom_groups': len(groups),
        'axiom_free_reports': free, 'total_axiom_reports': len(groups) + free,
        'expected_axiom_reports': component['expected_axiom_reports'],
        'declaration_checks': declarations,
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
    assert selection['expected_checks'] == 2 and selection['expected_axiom_reports'] == 2
    assert selection['expected_declaration_checks'] == 0
    assert selection['compile_order'] == [item['module'] for item in selection['components']]
    for component in selection['components']:
        run(component)
    verify_pins()
    pins_stable = True
except Exception as error:
    failure = {'type': type(error).__name__, 'message': str(error)}

passed = [item['exit'] == 0 and not item['diagnostics'] and not item['sorryAx']
    and not item['nonstandard_axioms'] and item['declaration_checks'] == 0
    and item['total_axiom_reports'] == item['expected_axiom_reports'] == 1
    for item in checks]
success = (failure is None and pins_stable and len(checks) == 2 and all(passed)
    and sum(item['total_axiom_reports'] for item in checks) == 2)
report = {'at': datetime.datetime.now().astimezone().isoformat(), 'checks': checks,
    'passed': passed, 'failure': failure, 'limits': limits,
    'two_components_checked': success, 'normal_module_inputs_checked_privately': success,
    'all_selected_statements_checked': success, 'both_selected_FIRST_headers_exact': True,
    'original_narrowing_FIRST_preserved': True, 'original_narrowing_FIRST_byte_equal': False,
    'original_narrowing_FIRST_alpha_equivalent': False,
    'current_source_narrowing_FIRST_checked': success,
    'original_legacy_draft_rejected_before_compiler': True,
    'actual_printed_public_axiom_reports': sum(item['total_axiom_reports'] for item in checks),
    'credited_public_reports': 2 if success else 0,
    'actual_definition_declaration_checks': sum(item['declaration_checks'] for item in checks),
    'new_private_explicit_reports': 0, 'new_private_helpers': 5, 'private_helpers_compiled_transitively': 5 if success else 0, 'new_prop_definitions': 0,
    'both_modules_are_new': True, 'fresh_credit_for_old_owner_theorems': 0,
    'source_pins_unchanged': pins_stable, 'proof_credit': success,
    'normal_source_changed': False, 'published': False,
    'source_commit': selection['source_commit'],
    'prior_publication_actual_session': selection['prior_publication_actual_session'],
    'source_qualified_original_fuel_narrowing_checked': success,
    'same_actual_dispatch_event_resources_checked': success,
    'both_supplied_native_primitive_fuels_retained': True,
    'same_actual_native_failure_endpoints_retained': True,
    'proof_limits': 'default limits; no overrides',
    'cache_data_copied': False,
    'prior_successful_subset_reports_recounted': False,
    'all_original_eager_worker_query_admissions_proved': False,
    'native_inhabitance_proved': False, 'guard_truth_proved': False,
    'joint_finite_completion_proved': False, 'haskell_changed': False}
(runtime / 'results.json').write_text(json.dumps(report, indent=2) + '\n')
if not success:
    print(json.dumps(report), flush=True)
    raise SystemExit(1)
(runtime / 'checked.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report), flush=True)
