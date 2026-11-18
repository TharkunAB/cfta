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
pins = json.loads((runtime / 'source-pins.json').read_text())
selection = json.loads((runtime / 'INHERITANCE-SELECTION.json').read_text())
checks = []
limits = {}
failure = None


def verify_pins():
    for name, digest in pins.items():
        assert hashlib.sha256((root / name).read_bytes()).hexdigest() == digest, name


def run(name, command, required_reports):
    verify_pins()
    (runtime / 'running.json').write_text(json.dumps({
        'name': name, 'at': datetime.datetime.now().astimezone().isoformat(),
    }) + '\n')
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
    declaration_checks = 0
    if name == 'strict-new-components-and-prior-bindings':
        declaration_checks = sum(len(re.findall(r'^' + re.escape(item) + r'(?=\s|\.?\{|\(|:)', output, re.M))
            for item in selection['definition_names'])
    item = {'name': name, 'exit': result.returncode, 'axiom_groups': len(groups),
        'axiom_free_reports': free, 'total_axiom_reports': len(groups) + free,
        'nonstandard_axioms': bad, 'diagnostics': len(re.findall(r': error(?:\(|:)', output)),
        'sorryAx': 'sorryAx' in output, 'declaration_checks': declaration_checks,
        'expected_reports': required_reports}
    checks.append(item)
    (runtime / 'checks.json').write_text(json.dumps(checks, indent=2) + '\n')
    print(json.dumps(item), flush=True)
    verify_pins()


jobs = [
    ('public-build', 'exec lake build', 0),
    ('strict-new-components-and-prior-bindings', 'exec python3 ' + shlex.quote(str(runtime / 'strict-new-and-bind.py')), 1),
    ('independent-imports', 'exec lake env lean -j1 -DwarningAsError=true ' + shlex.quote(str(runtime / 'IndependentProbes.lean')), 339),
    ('audit-build', 'exec lake build MicroCFTA.Audit', 0),
    ('audit-strict', 'exec lake env lean -j1 -DwarningAsError=true MicroCFTA/Audit.lean', 744),
]
try:
    assert not (runtime / 'checked.json').exists()
    group = next(line.split(':', 2)[2] for line in Path('/proc/self/cgroup').read_text().splitlines()
        if line.startswith('0::'))
    cgroup = Path('/sys/fs/cgroup') / group.lstrip('/')
    limits = {name: (cgroup / name).read_text().strip()
        for name in ['memory.max', 'memory.high', 'memory.swap.max']}
    assert limits == {'memory.max': '8589934592', 'memory.high': '8589934592', 'memory.swap.max': '0'}
    for name, command, required in jobs:
        run(name, command, required)
    assert len(checks) == 5
    assert all(item['exit'] == 0 and not item['nonstandard_axioms'] and not item['diagnostics']
        and not item['sorryAx'] and (not job[2] or item['total_axiom_reports'] == job[2])
        for item, job in zip(checks, jobs))
    assert checks[1]['axiom_groups'] == selection['fresh_axiom_groups']
    assert checks[1]['axiom_free_reports'] == selection['fresh_axiom_free_reports']
    assert checks[1]['declaration_checks'] == 1
    assert checks[2]['axiom_groups'] == selection['independent_axiom_groups']
    assert checks[2]['axiom_free_reports'] == selection['independent_axiom_free_reports']
    assert checks[4]['axiom_groups'] == selection['audit_axiom_groups']
    assert checks[4]['axiom_free_reports'] == selection['audit_axiom_free_reports']
    match = re.search(r'Checked axiom dependencies of (\d+) MicroCFTA theorems\.',
        (runtime / 'audit-strict.txt').read_text())
    assert match
    verify_pins()
except Exception as error:
    failure = {'type': type(error).__name__, 'message': str(error)}

if failure is not None:
    rejected = {'at': datetime.datetime.now().astimezone().isoformat(),
        'checks': checks, 'limits': limits, 'failure': failure,
        'all_five_gates_passed': False, 'proof_credit': False, 'published': False}
    (runtime / 'results.json').write_text(json.dumps(rejected, indent=2) + '\n')
    print(json.dumps(rejected), flush=True)
    raise SystemExit(1)
report = json.loads((runtime / 'REPORT-BASE.json').read_text())
report.update(checks=checks, limits=limits, at=datetime.datetime.now().astimezone().isoformat(),
    audited_theorems=int(match.group(1)), all_five_gates_passed=True,
    source_pins_unchanged=True)
(runtime / 'results.json').write_text(json.dumps(report, indent=2) + '\n')
(runtime / 'checked.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report), flush=True)
