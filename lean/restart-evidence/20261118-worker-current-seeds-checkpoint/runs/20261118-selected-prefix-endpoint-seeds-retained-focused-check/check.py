from pathlib import Path
import datetime
import hashlib
import json
import os
import re
import shlex
import subprocess
import tempfile

ROOT = Path('/home/tritlo/Code/mcfta')
RUN = Path(__file__).resolve().parent
pins = json.loads((RUN / 'source-pins.json').read_text())


def verify():
    for name, digest in pins.items():
        assert hashlib.sha256((ROOT / name).read_bytes()).hexdigest() == digest, name


verify()
assert not (RUN / 'results.json').exists()
group = next(line.split(':', 2)[2] for line in Path('/proc/self/cgroup').read_text().splitlines()
    if line.startswith('0::'))
cgroup = Path('/sys/fs/cgroup') / group.lstrip('/')
limits = {name: (cgroup / name).read_text().strip()
    for name in ['memory.max', 'memory.high', 'memory.swap.max']}
assert limits == {'memory.max': '8589934592', 'memory.high': '8589934592', 'memory.swap.max': '0'}
objects = Path(tempfile.mkdtemp(prefix='mcfta-selected-prefix-endpoint-seeds-focused-'))
(RUN / 'objects.json').write_text(json.dumps({'path': str(objects)}) + '\n')
environment = dict(os.environ)
environment.pop('LEAN_SYSROOT', None)
environment['LEAN_NUM_THREADS'] = '1'
command = 'exec lake env lean -j1 -DwarningAsError=true -R ' + shlex.quote(str(RUN))
command += ' -o ' + shlex.quote(str(objects / 'PrefixProbe.olean'))
command += ' ' + shlex.quote(str(RUN / 'PrefixProbe.lean'))
with (RUN / 'compiler.txt').open('w') as log:
    result = subprocess.run(['nix-shell', str(ROOT / 'shell.nix'), '--run', command],
        cwd=ROOT / 'lean', env=environment, stdout=log, stderr=subprocess.STDOUT, text=True)
verify()
output = (RUN / 'compiler.txt').read_text()
groups = [set(x.strip() for x in group.split(',') if x.strip())
    for group in re.findall(r'depends on axioms:\s*\[([^]]*)\]', output, re.S)]
free = len(re.findall(r'does not depend on any axioms', output))
bad = sorted(set().union(*groups) - {'propext', 'Classical.choice', 'Quot.sound'}) if groups else []
diagnostics = len(re.findall(r': error(?:\(|:)', output))
passed = result.returncode == 0 and len(groups) + free == 1 and not bad and not diagnostics
report = {'at': datetime.datetime.now().astimezone().isoformat(), 'exit': result.returncode,
    'axiom_groups': len(groups), 'axiom_free_reports': free, 'nonstandard_axioms': bad,
    'diagnostics': diagnostics, 'sorryAx': 'sorryAx' in output, 'passed': passed,
    'normal_Source_changed': False, 'source_pins_unchanged': True, 'limits': limits,
    'full_owning_module_checked': False, 'whole_fixed_batch_proof_credit': 0,
    'focused_elaboration_only': True}
(RUN / 'results.json').write_text(json.dumps(report, indent=2) + '\n')
if passed:
    (RUN / 'checked.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report))
raise SystemExit(0 if passed else 1)
