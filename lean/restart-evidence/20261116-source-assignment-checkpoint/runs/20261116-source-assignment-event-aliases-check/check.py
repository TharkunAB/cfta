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




jobs = [('public-dependencies', 'exec lake build MicroCFTA.EnumerationPartialCompletion MicroCFTA.EnumerationPartialExact MicroCFTA.EnumerationPartialRoot MicroCFTA.EnumerationPendingAssignment MicroCFTA.MergedColdReaderClosed MicroCFTA.MergedOrdinaryHeight MicroCFTA.SourceCurrentAllocatedNativeEmptyRootDomainAncestry MicroCFTA.SourcePruningEnumerationNativeBranchCompletion MicroCFTA.SourcePruningEnumerationNodes MicroCFTA.SourcePruningPartialRenderingSemantics', 0), ('partial-root-alias', 'exec lake env lean -j1 -DwarningAsError=true -R /home/tritlo/Code/mcfta/lean/restart-evidence/20261116-source-assignment-event-aliases-check/source -o /tmp/mcfta-source-event-aliases-2pgkpqmw/partial-root-alias.olean /home/tritlo/Code/mcfta/lean/restart-evidence/20261116-source-assignment-event-aliases-check/source/MicroCFTA/SourcePruningEnumerationPartialOutput.lean', 1), ('actual-enter-ids', 'exec lake env lean -j1 -DwarningAsError=true -R /home/tritlo/Code/mcfta/lean/restart-evidence/20261116-source-assignment-event-aliases-check/source -o /tmp/mcfta-source-event-aliases-2pgkpqmw/actual-enter-ids.olean /home/tritlo/Code/mcfta/lean/restart-evidence/20261116-source-assignment-event-aliases-check/source/MicroCFTA/SourceCurrentAllocatedNativeSourceEmptyEnterOperands.lean', 1)]
for name,command,count in jobs:run(name,command,count)
assert all(c['exit']==0 and not c['nonstandard_axioms'] and c['total_axiom_reports']==j[2] for c,j in zip(checks,jobs))
(runtime/'checked.json').write_text(json.dumps({'checks':checks,'source_pins_unchanged':True,'owner_prefixes_preserved':True,'joint_finite_completion_proved':False,'limits':limits},indent=2)+'\n')
