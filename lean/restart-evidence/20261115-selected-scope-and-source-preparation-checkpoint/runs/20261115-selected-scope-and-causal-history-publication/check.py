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
    item = {'name': name, 'exit': result.returncode, 'axiom_groups': len(groups), 'axiom_free_reports': free_reports, 'total_axiom_reports': len(groups) + free_reports, 'nonstandard_axioms': bad}
    checks.append(item)
    (runtime / 'checks.json').write_text(json.dumps(checks, indent=2) + '\n')
    print(json.dumps(item), flush=True)
    verify_pins()
    assert result.returncode == 0 and not bad and len(groups) + free_reports >= required_groups
    assert 'sorryAx' not in output



commands=[('public-build', 'exec lake build', 0), ('strict-changed-modules', 'exec python3 /home/tritlo/Code/mcfta/lean/restart-evidence/20261115-selected-scope-and-causal-history-publication/strict-modules.py', 0), ('independent-imports', 'exec lake env lean -j1 -DwarningAsError=true /home/tritlo/Code/mcfta/lean/restart-evidence/20261115-selected-scope-and-causal-history-publication/Imports.lean', 3), ('audit-build', 'exec lake build MicroCFTA.Audit', 195), ('audit-strict', 'exec lake env lean -j1 -DwarningAsError=true MicroCFTA/Audit.lean', 195)]
for name,command,count in commands:
    run(name,command,count)
match=re.search(r"Checked axiom dependencies of (\d+) MicroCFTA theorems\.",(runtime/"audit-strict.txt").read_text())
assert match and checks[-1]["total_axiom_reports"]==195
report={"at":datetime.datetime.now().astimezone().isoformat(),"limits":limits,"checks":checks,"audited_theorems":int(match.group(1)),"individual_reports":195,"source_pins_unchanged":True,"actual_selected_own_scope_push_proved":True,"actual_original_row_forecasts_proved":True,"actual_write_finalize_callback_clear_segment_proved":True,"whole_source_task_induction_proved":False,"all_fuel_worker_history_proved":False,"joint_finite_completion_proved":False,"haskell_changed":False}
(runtime/"checked.json").write_text(json.dumps(report,indent=2)+"\n")
print(json.dumps(report),flush=True)
