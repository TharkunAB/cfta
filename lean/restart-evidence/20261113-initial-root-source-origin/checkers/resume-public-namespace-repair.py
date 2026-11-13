from pathlib import Path
import datetime
import hashlib
import json
import os
import re
import shlex
import subprocess

root = Path('/home/tritlo/Code/mcfta')
base = Path(__file__).parent
prior = base / 'full-public'
runtime = base / 'namespace-repair'
runtime.mkdir(exist_ok=False)
before = (prior / 'source-pins.txt').read_text()
sha = lambda raw: hashlib.sha256(raw).hexdigest()
def snapshot():
    return '\n'.join(p.name + ' ' + sha(p.read_bytes())
                     for p in sorted((root / 'lean/MicroCFTA').glob('*.lean'))) + '\n'
assert snapshot() == before
cg = next(line.split(':', 2)[2] for line in Path('/proc/self/cgroup').read_text().splitlines()
          if line.startswith('0::'))
directory = Path('/sys/fs/cgroup') / cg.lstrip('/')
limits = {name: (directory / name).read_text().strip()
          for name in ['memory.max', 'memory.high', 'memory.swap.max']}
assert limits == {'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}
environment = dict(os.environ)
environment.pop('LEAN_SYSROOT', None)
environment['LEAN_NUM_THREADS'] = '1'
results = json.loads((prior / 'partial-report.json').read_text())[:3]
assert all(item['exit'] == 0 for item in results)
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
def run(name, command, minimum):
    outcome = subprocess.run(['nix-shell', str(root / 'shell.nix'), '--run', command],
                             cwd=root / 'lean', env=environment, capture_output=True, text=True)
    output = outcome.stdout + outcome.stderr
    (runtime / (name + '.txt')).write_text(output)
    groups = [set(x.strip() for x in group.split(',') if x.strip())
              for group in re.findall(r'depends on axioms:\s*\[([^]]*)\]', output, re.S)]
    results.append({'name': name, 'exit': outcome.returncode, 'axiom_groups': len(groups),
                    'nonstandard_axioms': sorted(set().union(*groups) - allowed) if groups else []})
    (runtime / 'partial-report.json').write_text(json.dumps(results, indent=2) + '\n')
    assert outcome.returncode == 0 and len(groups) >= minimum
    assert 'sorryAx' not in output and not results[-1]['nonstandard_axioms']

names = {
    'SourceSynthesisCurrentCandidateAppOperands': ['MicroCFTA.SourceSynthesisCurrentCandidateAppOperands.current_candidate_app_operands'],
    'SourceSynthesisCurrentInitialOuterNarrowRows': ['MicroCFTA.SourceSynthesisCurrentInitialOuterNarrowRows.initial_outer_narrow_rows'],
    'SourceSynthesisCurrentInitialFilterInterval': ['MicroCFTA.SourceSynthesisCurrentFirstFilterSourceLink.current_initial_filter_interval',
        'MicroCFTA.SourceSynthesisCurrentFirstFilterSourceLink.current_narrowed_filter_interval'],
    'SourceSynthesisCurrentCandidateSourceApp': ['MicroCFTA.SourceSynthesisCurrentFirstFilterSourceLink.current_candidate_source_app'],
}
for module in ['SourceSynthesisCurrentInitialFilterInterval', 'SourceSynthesisCurrentCandidateSourceApp']:
    text = (root / 'lean/MicroCFTA' / (module + '.lean')).read_text()
    text += ''.join('\n#print axioms ' + name + '\n' for name in names[module])
    path = runtime / (module + '.lean')
    path.write_text(text)
    run(module + '-strict-correct-namespace', 'exec lake env lean -j1 -DwarningAsError=true ' + shlex.quote(str(path)), len(names[module]))
probe = ''.join('import MicroCFTA.' + module + '\n' for module in names)
for declarations in names.values():
    for name in declarations:
        probe += '\n#check ' + name + '\n#print axioms ' + name + '\n'
path = runtime / 'public-import-check.lean'
path.write_text(probe)
run('public-import-check', 'exec lake env lean -j1 -DwarningAsError=true ' + shlex.quote(str(path)), 5)
path = runtime / 'Audit.lean'
path.write_bytes((root / 'lean/MicroCFTA/Audit.lean').read_bytes())
run('full-audit-strict', 'exec lake env lean -j1 -DwarningAsError=true ' + shlex.quote(str(path)), 1)
counts = re.findall(r'Checked axiom dependencies of (\d+) MicroCFTA theorems',
                    (runtime / 'full-audit-strict.txt').read_text())
assert len(counts) == 1 and int(counts[0]) >= 94957
assert snapshot() == before
report = {'at': datetime.datetime.now().astimezone().isoformat(), 'limits': limits,
          'live_modules': len(before.splitlines()), 'source_tree_sha256': sha(before.encode()),
          'audit_imports': sum(line.startswith('import ') for line in path.read_text().splitlines()),
          'audited_theorems': int(counts[0]), 'checks': results,
          'namespace_instrumentation_repaired': True, 'passed_checks_repeated': False,
          'haskell_changes': False, 'joint_completion_proved': False}
(runtime / 'checked.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report))
