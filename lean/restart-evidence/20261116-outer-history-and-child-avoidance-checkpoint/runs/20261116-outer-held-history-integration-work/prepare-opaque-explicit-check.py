from pathlib import Path
import hashlib
import json
import shlex
import tempfile

root = Path('/home/tritlo/Code/mcfta')
base = root / 'lean/restart-evidence'
run = base / '20261116-opaque-explicit-receipt-held-history-check'
run.mkdir()
owner = root / 'lean/MicroCFTA/SourcePruningEnumerationSharedEagerReservation.lean'
assert hashlib.sha256(owner.read_bytes()).hexdigest() == 'b5ac50c040b628920a02e12766f54a1508f3cc1ff3c9de049648633415cb8331'
packet = base / '20261116-current-real-opaque-terminal-held-history-explicit-child-receipt-repair'
appendix = packet / 'APPEND.lean.txt'
assert hashlib.sha256(appendix.read_bytes()).hexdigest() == 'bac45a0045301e2144b969c3c2e15d5d4d80a6660d6e2a38cecef60c83fbe9cb'
probes = packet / 'PROBES.lean.txt'
assert probes.read_bytes().count(b'#print axioms ') == 2
raw = owner.read_bytes() + b'\n' + appendix.read_bytes()
source = run / 'source/MicroCFTA' / owner.name
source.parent.mkdir(parents=True)
source.write_bytes(raw + b'\n' + probes.read_bytes())
objects = Path(tempfile.mkdtemp(prefix='mcfta-opaque-explicit-receipt-history-'))
(run / 'objects.json').write_text(json.dumps({'path': str(objects)}, indent=2) + '\n')
imports = sorted({line.split()[1] for line in raw.decode().splitlines() if line.startswith('import ')})
command = 'exec lake env lean -j1 -DwarningAsError=true -R ' + shlex.quote(str(source.parent.parent))
command += ' -o ' + shlex.quote(str(objects / 'Opaque.olean')) + ' ' + shlex.quote(str(source))
jobs = [('public-dependencies', 'exec lake build ' + ' '.join(imports), 0), ('opaque-explicit-receipt', command, 2)]
template = (base / '20261116-prefix-opaque-and-row-held-history-check/check.py').read_text()
driver = template[:template.index('\njobs =')]
driver += '\njobs = ' + repr(jobs) + '''
for name, command, count in jobs:
    run(name, command, count)
passed = [c['exit'] == 0 and not c['nonstandard_axioms'] and not c['diagnostics'] and not c['sorryAx'] and (not job[2] or c['total_axiom_reports'] == job[2])
          for c, job in zip(checks, jobs)]
report = {'checks': checks, 'passed': passed, 'source_pins_unchanged': True,
          'outer_depth_history_proved': False, 'joint_finite_completion_proved': False,
          'source_publication_pending': True, 'haskell_changed': False, 'limits': limits}
(runtime / 'results.json').write_text(json.dumps(report, indent=2) + '\\n')
assert len(checks) == 2 and all(passed)
(runtime / 'checked.json').write_text(json.dumps(report, indent=2) + '\\n')
print(json.dumps(report), flush=True)
'''
(run / 'check.py').write_text(driver)
files = list((root / 'lean/MicroCFTA').glob('*.lean'))
files += [root / n for n in ['shell.nix', 'lean/lean-toolchain', 'lean/lakefile.toml', 'lean/lake-manifest.json']]
files += [p for p in packet.iterdir() if p.is_file()]
files += [source, run / 'check.py', Path(__file__)]
(run / 'source-pins.json').write_text(json.dumps({str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest() for p in files}, indent=2) + '\n')
print(json.dumps({'run': str(run), 'objects': str(objects), 'reports': 2}))
