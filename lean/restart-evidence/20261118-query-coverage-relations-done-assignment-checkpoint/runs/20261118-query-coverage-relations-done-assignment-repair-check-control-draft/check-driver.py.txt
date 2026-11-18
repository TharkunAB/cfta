from pathlib import Path
import datetime
import hashlib
import json
import os
import re
import shlex
import subprocess

ROOT = Path('/home/tritlo/Code/mcfta')
runtime = Path(__file__).resolve().parent
s = json.loads((runtime / 'selection.json').read_text())
pins = json.loads((runtime / 'source-pins.json').read_text())
checks = []
limits = {}
failure = None
stable = False


def verify_pins():
    for name, digest in pins.items():
        assert hashlib.sha256((ROOT / name).read_bytes()).hexdigest() == digest, name


def run(item):
    verify_pins()
    name = item['module']
    (runtime / 'running.json').write_text(json.dumps({'name': name,
        'at': datetime.datetime.now().astimezone().isoformat()}) + '\n')
    env = dict(os.environ)
    env.pop('LEAN_SYSROOT', None)
    env['LEAN_NUM_THREADS'] = '1'
    command = 'exec lake env python3 ' + shlex.quote(str(runtime / 'shadow-compile.py')) + ' ' + shlex.quote(name)
    path = runtime / (name + '.txt')
    with path.open('w') as output:
        result = subprocess.run(['nix-shell', str(ROOT / 'shell.nix'), '--run', command],
            cwd=ROOT / 'lean', env=env, stdout=output, stderr=subprocess.STDOUT, text=True)
    text = path.read_text()
    groups = [set(x.strip() for x in group.split(',') if x.strip())
        for group in re.findall(r'depends on axioms:\s*\[([^]]*)\]', text, re.S)]
    free = len(re.findall(r'does not depend on any axioms', text))
    bad = sorted(set().union(*groups) - {'propext', 'Classical.choice', 'Quot.sound'}) if groups else []
    counts = {}
    private_prefix = r'(?:_private\.MicroCFTA\.SourcePruningEnumerationSharedEagerReservation\.\d+\.)?'
    for qname in item['definition_qnames']:
        pattern = r'^' + private_prefix + re.escape(qname) + r'(?=\s|:|\.\{)'
        counts[qname] = len(re.findall(pattern, text, re.M))
    record = {'name': name, 'report_kind': item['report_kind'], 'exit': result.returncode,
        'axiom_groups': len(groups), 'axiom_free_reports': free, 'total_axiom_reports': len(groups) + free,
        'expected_axiom_reports': item['expected_axiom_reports'], 'nonstandard_axioms': bad,
        'diagnostics': len(re.findall(r': error(?:\(|:)', text)), 'sorryAx': 'sorryAx' in text,
        'definition_checks_by_qname': counts, 'declaration_checks': sum(counts.values()),
        'expected_declaration_checks': item['expected_declaration_checks']}
    checks.append(record)
    (runtime / 'checks.json').write_text(json.dumps(checks, indent=2) + '\n')
    print(json.dumps(record), flush=True)
    verify_pins()


try:
    assert not (runtime / 'checked.json').exists()
    group = next(line.split(':', 2)[2] for line in Path('/proc/self/cgroup').read_text().splitlines() if line.startswith('0::'))
    cgroup = Path('/sys/fs/cgroup') / group.lstrip('/')
    limits = {name: (cgroup / name).read_text().strip() for name in ['memory.max', 'memory.high', 'memory.swap.max']}
    assert limits == {'memory.max': '8589934592', 'memory.high': '8589934592', 'memory.swap.max': '0'}
    assert s['expected_checks'] == 2 and s['expected_axiom_reports'] == 1
    assert s['expected_public_reports'] == 1 and s['expected_private_reports'] == 0
    assert s['expected_definition_checks'] == s['new_private_Prop_inductives'] == 4
    assert s['new_helpers'] == 0
    items = {item['module']: item for item in s['components']}
    assert len(items) == len(s['compile_order']) == 2 and set(items) == set(s['compile_order'])
    for name in s['compile_order']:
        run(items[name])
    verify_pins()
    stable = True
except Exception as error:
    failure = {'type': type(error).__name__, 'message': str(error)}
passed = [c['exit'] == 0 and not c['diagnostics'] and not c['sorryAx'] and not c['nonstandard_axioms']
    and c['total_axiom_reports'] == c['expected_axiom_reports']
    and c['declaration_checks'] == c['expected_declaration_checks']
    and all(count == 1 for count in c['definition_checks_by_qname'].values()) for c in checks]
success = failure is None and stable and len(checks) == 2 and all(passed)
success = success and sum(c['total_axiom_reports'] for c in checks) == 1
success = success and sum(c['declaration_checks'] for c in checks) == 4
report = {'at': datetime.datetime.now().astimezone().isoformat(), 'checks': checks, 'passed': passed,
    'failure': failure, 'limits': limits, 'source_pins_unchanged': stable,
    'all_selected_statements_checked': success, 'proof_credit': success,
    'credited_public_reports': 1 if success else 0, 'credited_private_reports': 0,
    'new_public_theorems': 1, 'new_private_theorems': 0, 'new_helpers': 0,
    'new_private_Prop_inductives': 4, 'new_constructors': 36,
    'actual_definition_declaration_checks': sum(c['declaration_checks'] for c in checks),
    'definition_axiom_credit': 0, 'prior_Source68_three_proofs_extra_credit': 0,
    'prior_Source67_fifteen_proofs_extra_credit': 0, 'normal_Source_changed': False, 'published': False,
    'source_commit': s['source_commit'], 'coverage_relations_checked': success,
    'conditional_current_done_assignment_checked': success, 'coverage_producer_proved': False,
    'complete_eager_worker_query_log_proved': False, 'guard_truth_proved': False,
    'historical_joint_assignment_proved': False, 'joint_finite_completion_proved': False,
    'haskell_changed': False, 'cache_data_copied': False}
(runtime / 'results.json').write_text(json.dumps(report, indent=2) + '\n')
if not success:
    print(json.dumps(report), flush=True)
    raise SystemExit(1)
(runtime / 'checked.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report), flush=True)
