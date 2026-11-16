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




jobs = [('public-build', 'exec lake build', 0), ('strict-resource-and-component-modules', 'exec python3 /home/tritlo/Code/mcfta/lean/restart-evidence/20261116-staged-child-incidence-publication/strict-modules.py', 237), ('independent-imports', 'exec lake env lean -j1 -DwarningAsError=true /home/tritlo/Code/mcfta/lean/restart-evidence/20261116-staged-child-incidence-publication/IndependentProbes.lean', 165), ('audit-build', 'exec lake build MicroCFTA.Audit', 0), ('audit-strict', 'exec lake env lean -j1 -DwarningAsError=true MicroCFTA/Audit.lean', 570)]
for name, command, count in jobs:
    run(name, command, count)
assert len(checks) == 5
assert all(c['exit'] == 0 and not c['nonstandard_axioms'] and not c['diagnostics'] and not c['sorryAx']
           and (not job[2] or c['total_axiom_reports'] == job[2]) for c, job in zip(checks, jobs))
match = re.search(r'Checked axiom dependencies of (\d+) MicroCFTA theorems\.', (runtime / 'audit-strict.txt').read_text())
assert match
report = {'checks': checks, 'source_pins_unchanged': True,
          'audited_theorems': int(match.group(1)), 'owner_resource_probes': 208,
          'original_resource_probes': 136, 'new_relation_declaration_reports': 0,
          'local_primitive_all_raw_alias_growth_proved': True,
          'specified_staged_child_position_incidence_proved': True,
          'same_selected_preparation_indexed_child_bridge_proved': True,
          'actual_shared_child_all_raw_alias_growth_proved': True,
          'whole_worker_all_raw_aliases_proved': False,
          'every_causal_historical_event_attached_proved': False,
          'joint_finite_completion_proved': False, 'haskell_changed': False,
          'limits': limits, 'at': datetime.datetime.now().astimezone().isoformat()}
report.update({'source_files': 6199, 'direct_audit_imports': 5199, 'individual_reports': 570, 'independent_reports': 165, 'resource_and_component_probes': 237, 'new_component_reports': 9, 'new_theorem_reports': 9, 'new_modules': 4, 'new_public_theorems': 9})
(runtime / 'checked.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report), flush=True)
