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



commands=[('public-build', 'exec lake build MicroCFTA.SourceSynthesisCurrentSharedSourceGoalFreshSlot MicroCFTA.SourceSynthesisCurrentSharedGoalSingletonPrefix', 0), ('SourceSynthesisCurrentSharedSourceGoalFreshSlot-strict', 'exec lake env lean -j1 -DwarningAsError=true MicroCFTA/SourceSynthesisCurrentSharedSourceGoalFreshSlot.lean', 0), ('SourceSynthesisCurrentSharedGoalSingletonPrefix-strict', 'exec lake env lean -j1 -DwarningAsError=true MicroCFTA/SourceSynthesisCurrentSharedGoalSingletonPrefix.lean', 0), ('independent-imports', 'exec lake env lean -j1 -DwarningAsError=true /home/tritlo/Code/mcfta/lean/restart-evidence/20261114-source-goal-prefix-publication/Imports.lean', 2), ('audit-build', 'exec lake build MicroCFTA.Audit', 187), ('audit-strict', 'exec lake env lean -j1 -DwarningAsError=true MicroCFTA/Audit.lean', 187)]
for name,command,count in commands:
    run(name,command,count)
audit=(runtime/"audit-strict.txt").read_text()
match=re.search(r"Checked axiom dependencies of (\d+) MicroCFTA theorems\.",audit)
assert match and checks[-1]["total_axiom_reports"]==187
report={"at":datetime.datetime.now().astimezone().isoformat(),"limits":limits,"checks":list(checks),"audited_theorems":int(match.group(1)),"individual_reports":187,"source_pins_unchanged":True,"source_goal_fresh_slot_proved":True,"actual_singleton_prefix_shared_fold_proved":True,"whole_first_goal_visit_producer_proved":False,"all_fuel_worker_history_proved":False,"joint_finite_completion_proved":False,"haskell_changed":False}
(runtime/"checked.json").write_text(json.dumps(report,indent=2)+"\n")
print(json.dumps(report),flush=True)

private_commands=[('position-admission-30', 'exec lake env lean -j1 -DwarningAsError=true -R /home/tritlo/Code/mcfta/lean/restart-evidence/20261114-source-goal-prefix-publication/source -o /tmp/mcfta-source-goal-composition-wy5eqtm9/objects/MicroCFTA/SourcePruningEnumerationSharedEagerReservation.olean /home/tritlo/Code/mcfta/lean/restart-evidence/20261114-source-goal-prefix-publication/source/MicroCFTA/SourcePruningEnumerationSharedEagerReservation.lean', 30), ('source-goal-first-child-1', 'exec lake env lean -j1 -DwarningAsError=true -R /home/tritlo/Code/mcfta/lean/restart-evidence/20261114-source-goal-prefix-publication/source -o /tmp/mcfta-source-goal-composition-wy5eqtm9/objects/MicroCFTA/SourceSynthesisCurrentSharedRootGoalFirstChild.olean /home/tritlo/Code/mcfta/lean/restart-evidence/20261114-source-goal-prefix-publication/source/MicroCFTA/SourceSynthesisCurrentSharedRootGoalFirstChild.lean', 1), ('prepared-written-path-origins-1', 'exec lake env lean -j1 -DwarningAsError=true -R /home/tritlo/Code/mcfta/lean/restart-evidence/20261114-source-goal-prefix-publication/source -o /tmp/mcfta-source-goal-composition-wy5eqtm9/objects/MicroCFTA/SourcePruningEnumerationPreparedSharedWrittenPathOrigins.olean /home/tritlo/Code/mcfta/lean/restart-evidence/20261114-source-goal-prefix-publication/source/MicroCFTA/SourcePruningEnumerationPreparedSharedWrittenPathOrigins.lean', 1)]
failed=[]
for name,command,count in private_commands:
    try:
        run(name,command,count)
    except AssertionError:
        verify_pins()
        failed.append(name)
private_report={"at":datetime.datetime.now().astimezone().isoformat(),"checks":checks[len(commands):],"limits":limits,"source_pins_unchanged":True,"failed_modules":failed,"all_fuel_worker_history_proved":False,"joint_finite_completion_proved":False}
(runtime/"private-checked.json").write_text(json.dumps(private_report,indent=2)+"\n")
print(json.dumps(private_report),flush=True)
assert not failed
