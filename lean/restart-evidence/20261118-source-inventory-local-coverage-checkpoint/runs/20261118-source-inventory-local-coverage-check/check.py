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
STANDARD = {'propext', 'Classical.choice', 'Quot.sound'}


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
    matches = list(re.finditer(r"^'([^'\n]+)' (?:depends on axioms:\s*\[([^]]*)\]|(does not depend on any axioms))", text, re.M))
    expected = item['private_qnames'] + item['public_qnames']
    classification = {}
    unexpected = []
    bad = set()
    for match in matches:
        resolved = match.group(1)
        axioms = sorted(set(x.strip() for x in (match.group(2) or '').split(',') if x.strip()))
        bad.update(set(axioms) - STANDARD)
        candidates = [qname for qname in expected if resolved == qname or
            (qname in item['private_qnames'] and re.fullmatch(
                r'_private\.MicroCFTA\.' + re.escape(name) + r'\.\d+\.' + re.escape(qname), resolved))]
        if len(candidates) != 1 or candidates[0] in classification:
            unexpected.append(resolved)
            continue
        qname = candidates[0]
        classification[qname] = {'resolved_qname': resolved, 'axioms': axioms,
            'axiom_free': match.group(3) is not None, 'private': qname in item['private_qnames']}
    groups = len(re.findall(r'depends on axioms:\s*\[', text))
    free = len(re.findall(r'does not depend on any axioms', text))
    record = {'name': name, 'report_kind': item['report_kind'], 'exit': result.returncode,
        'axiom_groups': groups, 'axiom_free_reports': free, 'total_axiom_reports': groups + free,
        'expected_axiom_reports': item['expected_axiom_reports'], 'nonstandard_axioms': sorted(bad),
        'diagnostics': len(re.findall(r': error(?:\(|:)', text)), 'sorryAx': 'sorryAx' in text,
        'classification_by_qname': classification, 'unexpected_or_duplicate_qnames': unexpected,
        'exact_selected_qnames': set(classification) == set(expected) and len(matches) == len(expected),
        'private_reports': sum(value['private'] for value in classification.values()),
        'public_reports': sum(not value['private'] for value in classification.values()),
        'expected_private_reports': item['expected_private_axiom_reports'],
        'expected_public_reports': item['expected_public_axiom_reports'],
        'declaration_checks': 0, 'expected_declaration_checks': 0}
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
    assert s['expected_checks'] == 3 and s['expected_axiom_reports'] == 4
    assert s['expected_public_reports'] == s['expected_private_reports'] == 2
    assert s['new_definitions'] == s['new_helpers'] == s['expected_definition_checks'] == 0
    items = {item['module']: item for item in s['components']}
    assert len(items) == len(s['compile_order']) == 3 and set(items) == set(s['compile_order'])
    for name in s['compile_order']:
        run(items[name])
    verify_pins()
    stable = True
except Exception as error:
    failure = {'type': type(error).__name__, 'message': str(error)}
passed = [c['exit'] == 0 and not c['diagnostics'] and not c['sorryAx'] and not c['nonstandard_axioms']
    and c['total_axiom_reports'] == c['expected_axiom_reports'] and c['exact_selected_qnames']
    and not c['unexpected_or_duplicate_qnames']
    and c['private_reports'] == c['expected_private_reports']
    and c['public_reports'] == c['expected_public_reports'] for c in checks]
success = failure is None and stable and len(checks) == 3 and all(passed)
success = success and [c['total_axiom_reports'] for c in checks] == [2, 1, 1]
report = {'at': datetime.datetime.now().astimezone().isoformat(), 'checks': checks, 'passed': passed,
    'failure': failure, 'limits': limits, 'source_pins_unchanged': stable,
    'all_selected_statements_checked': success, 'proof_credit': success,
    'credited_public_reports': 2 if success else 0, 'credited_private_reports': 2 if success else 0,
    'new_public_theorems': 2, 'new_private_theorems': 2, 'new_helpers': 0,
    'new_definitions': 0, 'definition_checks': 0, 'definition_axiom_credit': 0,
    'rebuilt_Source69_proofs_relations_extra_credit': 0, 'old_Mu22743_repeat_additive_credit': 0,
    'normal_Source_changed': False, 'published': False, 'source_commit': s['source_commit'],
    'full_coverage_producer334c_proved': False, 'complete_eager_worker_query_log_proved': False,
    'all_worker_admissions_proved': False, 'guard_truth_proved': False,
    'historical_joint_assignment_proved': False, 'joint_finite_completion_proved': False,
    'haskell_changed': False, 'cache_data_copied': False}
(runtime / 'results.json').write_text(json.dumps(report, indent=2) + '\n')
if not success:
    print(json.dumps(report), flush=True)
    raise SystemExit(1)
(runtime / 'checked.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report), flush=True)
