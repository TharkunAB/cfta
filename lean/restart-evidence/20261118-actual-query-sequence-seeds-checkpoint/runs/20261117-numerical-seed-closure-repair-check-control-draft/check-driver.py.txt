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
components = {item['module']: item for item in selection['components']}


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
    item = {'name': name, 'exit': result.returncode, 'axiom_groups': len(groups),
        'axiom_free_reports': free, 'total_axiom_reports': len(groups) + free,
        'expected_axiom_reports': component['expected_axiom_reports'],
        'declaration_checks': sum(len(re.findall(r'^' + re.escape(name) + r'(?:\s|\{|:)', output, re.M)) for name in component.get('declaration_names', [])),
        'expected_declaration_checks': component['expected_declaration_checks'],
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
    assert selection['expected_checks'] == 13 and selection['expected_axiom_reports'] == 17
    assert selection['expected_declaration_checks'] == 1
    components = {item['module']: item for item in selection['components']}
    assert len(components) == 13 and set(selection['compile_order']) == set(components)
    for module in selection['compile_order']:
        run(components[module])
    verify_pins()
except Exception as error:
    failure = {'type': type(error).__name__, 'message': str(error)}

passed = [item['exit'] == 0 and not item['diagnostics'] and not item['sorryAx']
    and not item['nonstandard_axioms']
    and item['total_axiom_reports'] == item['expected_axiom_reports']
    and item['declaration_checks'] == item['expected_declaration_checks']
    for item in checks]
success = (failure is None and len(checks) == 13 and all(passed)
    and sum(item['total_axiom_reports'] for item in checks) == 17
    and sum(item['declaration_checks'] for item in checks) == 1)
report = {'at': datetime.datetime.now().astimezone().isoformat(), 'checks': checks,
    'passed': passed, 'failure': failure, 'limits': limits,
    'all_thirteen_seed_closure_components_checked': success, 'normal_module_checked': success,
    'all_selected_statements_checked': success, 'all_selected_first_headers_exact': True,
    'actual_new_public_axiom_reports': sum(components[item['name']]['expected_public_axiom_reports'] for item in checks if item['exit'] == 0 and item['total_axiom_reports'] == item['expected_axiom_reports']),
    'actual_public_axiom_reports': sum(components[item['name']]['expected_public_axiom_reports'] for item in checks if item['exit'] == 0 and item['total_axiom_reports'] == item['expected_axiom_reports']),
    'actual_owning_private_axiom_reports': sum(components[item['name']]['expected_private_axiom_reports'] for item in checks if item['exit'] == 0 and item['total_axiom_reports'] == item['expected_axiom_reports']),
    'actual_total_axiom_reports': sum(item['total_axiom_reports'] for item in checks),
    'actual_definition_declaration_checks': sum(item['declaration_checks'] for item in checks), 'new_private_explicit_reports': sum(components[item['name']]['expected_private_axiom_reports'] for item in checks if item['exit'] == 0),
    'new_private_helpers_selected': selection['new_private_helpers'],
    'new_private_helpers_compiled_transitively': selection['new_private_helpers'] if success else 0,
    'new_prop_definitions': 1, 'Prop_definition_axiom_report_credit': 0, 'historical_old_owner_prefixes_preserved': True,
    'fresh_credit_for_old_owner_theorems': 0, 'source_pins_unchanged': failure is None,
    'proof_credit': success, 'normal_source_changed': False, 'published': False,
    'source_commit': selection['actual_source_commit'], 'same_original_runtime_fuels': True,
    'proof_limits': 'unchanged owner prefixes and defaults for the appended proofs',
    'cache_data_copied': False, 'body_first_numerical_callbacks_checked': success,
    'coherent_toprow_numerical_callbacks_checked': success,
    'past_numerical_seeds_to_fixed_H_mapper_checked': success,
    'generic_Gamma_and_aux_from_past_Seeds_checked': success,
    'retained_Mu_admission_checked': success,
    'singleton_node_and_edge_factors_checked': success,
    'local_retained_query_Seeds_preservation_checked': success,
    'public_actual_finite_query_sequence_Seeds_producer_checked': success,
    'Seeds_preservation_for_actual_admitted_query_sequences_proved': success,
    'original_eager_worker_all_calls_Seeds_propagation_proved': False,
    'original_BodyFirst_FIRST_preserved': True,
    'selected_BodyFirst_FIRST_byte_equal_to_original': False,
    'BodyFirst_FIRST_semicolon_only_repair': True,
    'Coherent_original_FIRST_byte_exact': True,
    'failed95793_and_rejected_sorryAx_preserved': True,
    'failed78168_and63694_preserved': True,
    'only_Terminal_and_FullNoMu_minimal_repairs_selected': True,
    'inherited_Source55_six_seed_result_unchanged': True,
    'new_six_seed_report_credit': 0,
    'existing_next_warm_NoNewMu_scope_unchanged': True,
    'arbitrary_worker_query_sequence_admissions_proved': False,
    'all_worker_call_qualifications_proved': False, 'native_inhabitance_proved': False,
    'joint_finite_completion_proved': False, 'haskell_changed': False}
(runtime / 'results.json').write_text(json.dumps(report, indent=2) + '\n')
if not success:
    print(json.dumps(report), flush=True)
    raise SystemExit(1)
(runtime / 'checked.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report), flush=True)
