from pathlib import Path
import hashlib
import json
import shlex
import tempfile

root = Path('/home/tritlo/Code/mcfta')
base = root / 'lean/restart-evidence'
run = base / '20261116-recompletion-local-levels-and-arrow-check'
run.mkdir()
specs = [('recompletion-algebra', '20261116-current-snapshot-recompletion-algebra-draft', 'EnumerationPendingRecompletion.lean', 'b31a5cdae554df95d9b6f470cda6aa6acc061eaf3f6cb77bf3f264301816fe63'), ('local-levels', '20261116-local-stratified-level-receipts-draft', 'EnumerationStratifiedLevelReceipts.lean', '300dee737eae62fc0bee7fe816b9c8fa6e1f0a5e8083ea77799d0085776c527c'), ('parametric-arrow', '20261116-parametric-arrow-bucket-recompletion-draft', 'SourcePruningEnumerationParametricArrowBucketWitness.lean', '917fef0f3ede719fe853654687994298b062a5e4607998e14eec535cb58b1b9d')]
objects = Path(tempfile.mkdtemp(prefix='mcfta-recompletion-local-levels-arrow-'))
(run / 'objects.json').write_text(json.dumps({'path': str(objects)}, indent=2) + '\n')
imports = set()
jobs = []
files = []
for label, folder, name, digest in specs:
    packet = base / folder
    raw = packet / name
    probes = packet / 'PROBES.lean.txt'
    assert hashlib.sha256(raw.read_bytes()).hexdigest() == digest
    count = probes.read_bytes().count(b'#print axioms ')
    assert count == {'recompletion-algebra': 2, 'local-levels': 2, 'parametric-arrow': 1}[label]
    source = run / 'source/MicroCFTA' / name
    source.parent.mkdir(parents=True, exist_ok=True)
    source.write_bytes(raw.read_bytes() + b'\n' + probes.read_bytes())
    imports.update(line.split()[1] for line in raw.read_text().splitlines() if line.startswith('import '))
    command = 'exec lake env lean -j1 -DwarningAsError=true -R ' + shlex.quote(str(source.parent.parent))
    command += ' -o ' + shlex.quote(str(objects / (label + '.olean'))) + ' ' + shlex.quote(str(source))
    jobs.append((label, command, count))
    files += [p for p in packet.iterdir() if p.is_file()]
    files.append(source)
jobs.insert(0, ('public-dependencies', 'exec lake build ' + ' '.join(sorted(imports)), 0))
template = (base / '20261116-full-outer-held-history-final-case-check/check.py').read_text()
driver = template[:template.index('\njobs =')]
driver += '\njobs = ' + repr(jobs) + '''
for name, command, count in jobs:
    run(name, command, count)
passed = [c['exit'] == 0 and not c['nonstandard_axioms'] and not c['diagnostics'] and not c['sorryAx'] and (not job[2] or c['total_axiom_reports'] == job[2])
          for c, job in zip(checks, jobs)]
report = {'checks': checks, 'passed': passed, 'source_pins_unchanged': True,
          'local_algebra_and_level_producers_only': True, 'actual_source_dependency_cut_proved': False,
          'joint_finite_completion_proved': False, 'haskell_changed': False, 'limits': limits}
(runtime / 'results.json').write_text(json.dumps(report, indent=2) + '\\n')
assert len(checks) == 4 and all(passed)
(runtime / 'checked.json').write_text(json.dumps(report, indent=2) + '\\n')
print(json.dumps(report), flush=True)
'''
(run / 'check.py').write_text(driver)
files += list((root / 'lean/MicroCFTA').glob('*.lean'))
files += [root / n for n in ['shell.nix', 'lean/lean-toolchain', 'lean/lakefile.toml', 'lean/lake-manifest.json']]
files += [Path(__file__), run / 'check.py']
(run / 'source-pins.json').write_text(json.dumps({str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest() for p in files}, indent=2) + '\n')
print(json.dumps({'run': str(run), 'objects': str(objects), 'module_reports': 5}))
