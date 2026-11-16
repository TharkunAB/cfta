from pathlib import Path
import hashlib
import json
import shlex
import tempfile

root = Path('/home/tritlo/Code/mcfta')
base = root / 'lean/restart-evidence'
run = base / '20261116-recompletion-binders-and-actual-finalizer-cut-check'
run.mkdir()
owner = root / 'lean/MicroCFTA/SourcePruningEnumerationSharedEagerReservation.lean'
assert hashlib.sha256(owner.read_bytes()).hexdigest() == '6baeb7f22592dc649710880135d93be3e36f47fee5abe30193f4fbb7cee4c2f4'
algebra = base / '20261116-current-snapshot-recompletion-algebra-binder-repair'
wrapper = base / '20261116-actual-child-finalizer-stratified-cut-draft'
assert hashlib.sha256((algebra / 'EnumerationPendingRecompletion.lean').read_bytes()).hexdigest() == '5cfea72aacc3ca1418afbeb6fee805067ed32d61acb0ee4dad20e722e816fae1'
assert hashlib.sha256((wrapper / 'APPEND.lean.txt').read_bytes()).hexdigest() == '97d176fc0d081871ddae219e4feddfe38574ea58b1ada619b16a2dc22da9f022'
specs = [
    ('recompletion-binder-repair', 'EnumerationPendingRecompletion.lean',
     (algebra / 'EnumerationPendingRecompletion.lean').read_bytes(), (algebra / 'PROBES.lean.txt').read_bytes(), 2),
    ('actual-finalizer-cut', owner.name,
     b'import MicroCFTA.EnumerationStratifiedLevelReceipts\n' + owner.read_bytes() + b'\n' + (wrapper / 'APPEND.lean.txt').read_bytes(),
     (wrapper / 'PROBES.lean.txt').read_bytes(), 1),
]
objects = Path(tempfile.mkdtemp(prefix='mcfta-recompletion-actual-finalizer-cut-'))
(run / 'objects.json').write_text(json.dumps({'path': str(objects)}, indent=2) + '\n')
imports = set()
jobs = []
files = [p for folder in [algebra, wrapper] for p in folder.iterdir() if p.is_file()]
for label, name, raw, probes, count in specs:
    assert probes.count(b'#print axioms ') == count
    source = run / 'source/MicroCFTA' / name
    source.parent.mkdir(parents=True, exist_ok=True)
    source.write_bytes(raw + b'\n' + probes)
    files.append(source)
    imports.update(line.split()[1] for line in raw.decode().splitlines() if line.startswith('import '))
    command = 'exec lake env lean -j1 -DwarningAsError=true -R ' + shlex.quote(str(source.parent.parent))
    command += ' -o ' + shlex.quote(str(objects / (label + '.olean'))) + ' ' + shlex.quote(str(source))
    jobs.append((label, command, count))
jobs.insert(0, ('public-dependencies', 'exec lake build ' + ' '.join(sorted(imports)), 0))
template = (base / '20261116-pending-evaluation-three-lemmas-check/check.py').read_text()
driver = template[:template.index('\njobs =')]
driver += '\njobs = ' + repr(jobs) + '''
for name, command, count in jobs:
    run(name, command, count)
passed = [c['exit'] == 0 and not c['nonstandard_axioms'] and not c['diagnostics'] and not c['sorryAx'] and (not job[2] or c['total_axiom_reports'] == job[2])
          for c, job in zip(checks, jobs)]
report = {'checks': checks, 'passed': passed, 'source_pins_unchanged': True,
          'local_algebra_and_actual_finalizer_only': True, 'whole_worker_cut_proved': False,
          'joint_finite_completion_proved': False, 'haskell_changed': False, 'limits': limits}
(runtime / 'results.json').write_text(json.dumps(report, indent=2) + '\\n')
assert len(checks) == 3 and all(passed)
(runtime / 'checked.json').write_text(json.dumps(report, indent=2) + '\\n')
print(json.dumps(report), flush=True)
'''
(run / 'check.py').write_text(driver)
files += list((root / 'lean/MicroCFTA').glob('*.lean'))
files += [root / n for n in ['shell.nix', 'lean/lean-toolchain', 'lean/lakefile.toml', 'lean/lake-manifest.json']]
files += [Path(__file__), run / 'check.py']
(run / 'source-pins.json').write_text(json.dumps({str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest() for p in files}, indent=2) + '\n')
print(json.dumps({'run': str(run), 'objects': str(objects), 'reports': 3}))
