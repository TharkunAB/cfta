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
    item = {'name': name, 'exit': result.returncode, 'axiom_groups': len(groups), 'axiom_free_reports': free_reports, 'total_axiom_reports': len(groups) + free_reports, 'nonstandard_axioms': bad, 'diagnostics': len(re.findall(r': error(?:\(|:)', output)), 'sorryAx': 'sorryAx' in output}
    checks.append(item)
    (runtime / 'checks.json').write_text(json.dumps(checks, indent=2) + '\n')
    print(json.dumps(item), flush=True)
    verify_pins()




jobs = [('SourceCurrentAllocatedNativeCompileDispatchOrigin', 'exec lake env python3 /home/tritlo/Code/mcfta/lean/restart-evidence/20261117-warm-actual-prefix-interfaces-first-check/shadow-compile.py SourceCurrentAllocatedNativeCompileDispatchOrigin', 1), ('SourceCurrentAllocatedNativeEdgeCompileDispatchOrigin', 'exec lake env python3 /home/tritlo/Code/mcfta/lean/restart-evidence/20261117-warm-actual-prefix-interfaces-first-check/shadow-compile.py SourceCurrentAllocatedNativeEdgeCompileDispatchOrigin', 1), ('SourceCurrentAllocatedNativeActualPrefixReturnedInduction', 'exec lake env python3 /home/tritlo/Code/mcfta/lean/restart-evidence/20261117-warm-actual-prefix-interfaces-first-check/shadow-compile.py SourceCurrentAllocatedNativeActualPrefixReturnedInduction', 1)]
for name, command, count in jobs:
    run(name, command, count)
passed = [item['exit'] == 0 and not item['diagnostics'] and not item['sorryAx']
    and not item['nonstandard_axioms'] and item['total_axiom_reports'] == 1 for item in checks]
report = {'checks': checks, 'passed': passed, 'source_pins_unchanged': True,
    'normal_module_checked': all(passed), 'normal_source_changed': False,
    'existing_owner_prefixes_byte_exact': True, 'new_public_reports': 3,
    'same_original_fuels': True, 'proof_limits': 'unchanged defaults for appended proofs',
    'source_semantic_callbacks_proved': False, 'joint_finite_completion_proved': False,
    'haskell_changed': False, 'limits': limits}
(runtime / 'results.json').write_text(json.dumps(report, indent=2) + '\n')
assert len(checks) == 3 and all(passed)
(runtime / 'checked.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report), flush=True)
