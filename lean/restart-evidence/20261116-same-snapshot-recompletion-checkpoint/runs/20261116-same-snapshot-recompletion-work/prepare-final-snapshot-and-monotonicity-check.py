from pathlib import Path
import hashlib
import json
import shlex
import tempfile

root = Path('/home/tritlo/Code/mcfta')
base = root / 'lean/restart-evidence'
work = Path(__file__).parent
algebra = base / '20261116-current-snapshot-recompletion-algebra-binder-repair'
checked = json.loads((base / '20261116-recompletion-binders-and-actual-finalizer-cut-check/checked.json').read_text())
assert all(checked['passed']) and checked['source_pins_unchanged']
source = algebra / 'EnumerationPendingRecompletion.lean'
assert hashlib.sha256(source.read_bytes()).hexdigest() == '5cfea72aacc3ca1418afbeb6fee805067ed32d61acb0ee4dad20e722e816fae1'
destination = root / 'lean/MicroCFTA' / source.name
assert not destination.exists()
destination.write_bytes(source.read_bytes())
(work / 'ALGEBRA-IMPORT-STAGING.json').write_text(json.dumps({
    'source': str(source.relative_to(root)), 'destination': str(destination.relative_to(root)),
    'sha256': hashlib.sha256(destination.read_bytes()).hexdigest(),
    'local_strict_check_passed': True, 'public_gates_pending': True,
}, indent=2) + '\n')
run = base / '20261116-final-snapshot-arrow-and-allocated-level-check'
run.mkdir()
specs = [
    ('same-snapshot-arrow', '20261116-final-snapshot-arrow-bucket-recompletion-draft',
     'SourcePruningEnumerationArrowBucketRecompletion.lean',
     'ab4154ec66e6531cdccbba97b818bdc335c4d7eb615e97fa2a66c574b4cab15a', 1),
    ('allocated-level-monotonicity', '20261116-stratified-allocated-level-monotonicity-draft',
     'EnumerationStratifiedAllocatedMonotonicity.lean',
     '1fe1d40e5a75a73a55eba79dc89c5fd58cc34399f608b2bed9cdad1366bdd90b', 1),
]
objects = Path(tempfile.mkdtemp(prefix='mcfta-final-snapshot-arrow-level-'))
(run / 'objects.json').write_text(json.dumps({'path': str(objects)}, indent=2) + '\n')
imports = set()
jobs = []
files = []
for label, packet, name, digest, count in specs:
    folder = base / packet
    raw = (folder / name).read_bytes()
    probes = (folder / 'PROBES.lean.txt').read_bytes()
    assert hashlib.sha256(raw).hexdigest() == digest
    assert probes.count(b'#print axioms ') == count
    candidate = run / 'source/MicroCFTA' / name
    candidate.parent.mkdir(parents=True, exist_ok=True)
    candidate.write_bytes(raw + b'\n' + probes)
    files.extend(p for p in folder.iterdir() if p.is_file())
    files.append(candidate)
    imports.update(line.split()[1] for line in raw.decode().splitlines() if line.startswith('import '))
    command = 'exec lake env lean -j1 -DwarningAsError=true -R ' + shlex.quote(str(candidate.parent.parent))
    command += ' -o ' + shlex.quote(str(objects / (label + '.olean'))) + ' ' + shlex.quote(str(candidate))
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
          'same_snapshot_arrow_and_allocated_level_only': True,
          'whole_worker_cut_proved': False, 'joint_finite_completion_proved': False,
          'haskell_changed': False, 'limits': limits}
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
print(json.dumps({'run': str(run), 'objects': str(objects), 'reports': 2}))
