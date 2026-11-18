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
checks, limits = [], {}
failure, pins_stable = None, False


def verify_pins():
    for name, digest in pins.items():
        assert hashlib.sha256((root / name).read_bytes()).hexdigest() == digest, name


def run(component):
    verify_pins()
    name = component['module']
    objects = Path(json.loads((runtime / 'objects.json').read_text())['path'])
    normal = (root / 'lean/.lake/build/lib/lean/MicroCFTA').resolve()
    assert not (objects / 'MicroCFTA' / (name + '.olean')).exists()
    for link in (objects / 'MicroCFTA').iterdir():
        assert link.is_symlink() and link.resolve().parent == normal, str(link)
    (runtime / 'running.json').write_text(json.dumps({'name': name,
        'at': datetime.datetime.now().astimezone().isoformat()}) + '\n')
    command = 'exec lake env python3 ' + shlex.quote(str(runtime / 'shadow-compile.py')) + ' ' + shlex.quote(name)
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
    qnames = re.findall(r"^'?([^'\n ]+)'? (?:depends on axioms:|does not depend on any axioms)", output, re.M)
    item = {'name': name, 'report_kind': 'public', 'exit': result.returncode,
        'axiom_groups': len(groups), 'axiom_free_reports': free, 'total_axiom_reports': len(groups) + free,
        'expected_axiom_reports': 1, 'expected_public_axiom_reports': 1, 'expected_private_axiom_reports': 0,
        'printed_qnames': qnames, 'expected_qnames': component['public_qnames'],
        'declaration_checks': 0, 'expected_declaration_checks': 0,
        'nonstandard_axioms': bad, 'diagnostics': len(re.findall(r': error(?:\(|:)', output)),
        'sorryAx': 'sorryAx' in output}
    checks.append(item)
    (runtime / 'checks.json').write_text(json.dumps(checks, indent=2) + '\n')
    print(json.dumps(item), flush=True)
    verify_pins()


try:
    assert not (runtime / 'checked.json').exists()
    group = next(line.split(':', 2)[2] for line in Path('/proc/self/cgroup').read_text().splitlines() if line.startswith('0::'))
    cgroup = Path('/sys/fs/cgroup') / group.lstrip('/')
    limits = {name: (cgroup / name).read_text().strip() for name in ['memory.max', 'memory.high', 'memory.swap.max']}
    assert limits == {'memory.max': '8589934592', 'memory.high': '8589934592', 'memory.swap.max': '0'}
    assert selection['expected_checks'] == len(selection['components']) == 1
    assert selection['expected_public_axiom_reports'] == selection['expected_total_axiom_reports'] == 1
    assert selection['expected_explicit_private_axiom_reports'] == selection['new_private_theorems'] == 0
    assert selection['expected_declaration_checks'] == selection['new_definitions'] == selection['new_private_helpers_transitive'] == 0
    assert selection['outside_Source68_and_Source69_selected_batches']
    component = selection['components'][0]
    assert selection['compile_order'] == [component['module']]
    run(component)
    verify_pins()
    pins_stable = True
except Exception as error:
    failure = {'type': type(error).__name__, 'message': str(error)}
passed = [item['exit'] == 0 and not item['diagnostics'] and not item['sorryAx']
    and not item['nonstandard_axioms'] and item['total_axiom_reports'] == 1
    and item['printed_qnames'] == item['expected_qnames'] for item in checks]
success = failure is None and pins_stable and len(checks) == 1 and all(passed)
report = {'at': datetime.datetime.now().astimezone().isoformat(), 'checks': checks,
    'passed': passed, 'failure': failure, 'limits': limits,
    'all_selected_statements_checked': success,
    'actual_printed_axiom_reports': sum(item['total_axiom_reports'] for item in checks),
    'expected_public_axiom_reports': 1, 'expected_explicit_private_axiom_reports': 0,
    'credited_public_reports': 1 if success else 0, 'credited_private_reports': 0,
    'new_public_theorems': 1, 'new_private_theorems': 0, 'new_private_helpers_transitive': 0,
    'new_definitions': 0, 'actual_definition_declaration_checks': 0, 'definition_axiom_credit': 0,
    'source_pins_unchanged': pins_stable, 'proof_credit': success,
    'source_commit': selection['source_commit'], 'prior_publication_actual_session': 32291,
    'prior_publication_pins_verified_by_preparer': 10829,
    'original_FIRST816bytes_and_entire_39line_proof_byte_exact': True,
    'conditional_closed_recursive_boundary_source_mu_record_checked': success,
    'source_record_has_same_resident_Mu_payload': True,
    'every_accepted_source_has_Mu_proved': False,
    'Done_assignment_generalization_proved': False,
    'Source69_credit': 0, 'Source69_results_assumed': False,
    'complete_eager_worker_query_log_proved': False,
    'all_original_query_admissions_proved': False,
    'historical_removed_or_parked_guard_truth_proved': False,
    'residual_guard_truth_proved': False, 'Type_Marker_joint_class_consistency_proved': False,
    'one_finite_accepted_original_root_completion_proved': False,
    'joint_finite_completion_proved': False, 'haskell_correspondence_proved': False,
    'outside_Source68_and_Source69_selected_batches': True,
    'normal_Source_changed': False, 'published': False, 'haskell_changed': False,
    'proof_limits': 'default; no override', 'cache_data_copied': False}
(runtime / 'results.json').write_text(json.dumps(report, indent=2) + '\n')
if not success:
    print(json.dumps(report), flush=True)
    raise SystemExit(1)
(runtime / 'checked.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report), flush=True)
