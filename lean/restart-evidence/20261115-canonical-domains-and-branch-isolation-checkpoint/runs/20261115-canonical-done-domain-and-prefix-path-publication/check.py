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



commands=[('public-build', 'exec lake build', 0), ('strict-changed-modules', 'exec python3 /home/tritlo/Code/mcfta/lean/restart-evidence/20261115-canonical-done-domain-and-prefix-path-publication/strict-modules.py', 0), ('independent-imports', 'exec lake env lean -j1 -DwarningAsError=true /home/tritlo/Code/mcfta/lean/restart-evidence/20261115-canonical-done-domain-and-prefix-path-publication/Imports.lean', 14), ('audit-build', 'exec lake build MicroCFTA.Audit', 224), ('audit-strict', 'exec lake env lean -j1 -DwarningAsError=true MicroCFTA/Audit.lean', 224)]
for name,command,count in commands:
    run(name,command,count)
match=re.search(r"Checked axiom dependencies of (\d+) MicroCFTA theorems\.",(runtime/"audit-strict.txt").read_text())
assert match and checks[-1]["total_axiom_reports"]==224
report={'individual_reports': 224, 'source_pins_unchanged': True, 'canonical_closed_union_mu_member_proved': True, 'grown_only_U_union_all_typeIn_members_proved': True, 'cold_source_union_member_and_no_mu_cases_proved': True, 'done_pending_type_members_from_endpoint_atoms_proved': True, 'actual_incoming_union_normal_all_budgets_outcomes_proved': True, 'arbitrary_depth_joint_prefix_free_bucket_one_assignment_proved': True, 'one_original_guard_projection_prefix_free_proved': True, 'strict_prefix_alias_no_finite_assignment_proved': True, 'whole_output_only_U_atoms_proved': False, 'whole_visitor_union_normal_proved': False, 'arbitrary_merged_bucket_compatibility_proved': False, 'same_branch_all_clear_history_extraction_proved': False, 'whole_output_satisfies_proved': False, 'joint_finite_completion_proved': False, 'haskell_changed': False}
report.update({"at":datetime.datetime.now().astimezone().isoformat(),"limits":limits,"checks":checks,"audited_theorems":int(match.group(1))})
(runtime/"checked.json").write_text(json.dumps(report,indent=2)+"\n")
print(json.dumps(report),flush=True)
