from pathlib import Path
import hashlib
import json
import shlex
import tempfile

root = Path('/home/tritlo/Code/mcfta')
base = root / 'lean/restart-evidence'
run = base / '20261116-pending-evaluation-three-lemmas-check'
run.mkdir()
specs = [
    ('congruence', '20261116-current-pending-evaluator-closed-set-congruence-draft', 'EnumerationPendingAssignmentCongruence.lean', '867da07cb60bf8b6392496d669b06f8a98f3c1ebfedad1042267c085c9fc6147'),
    ('fixed-point', '20261116-current-pending-evaluator-stored-equations-fixed-point-draft', 'EnumerationPendingAssignmentFixedPoint.lean', '53ee2b8e01a669eccc966b2ec744733539e329341c231cf4ff9d80b258ac7536'),
    ('explicit-witness', '20261116-current-pending-evaluation-explicit-witness-draft', 'EnumerationPendingEvaluationWitness.lean', 'd3fde5b55ba9126ff73a310a17102bcaf00934138aff7315ef753a9f1509b756'),
]
objects = Path(tempfile.mkdtemp(prefix='mcfta-pending-evaluation-three-lemmas-'))
(run / 'objects.json').write_text(json.dumps({'path': str(objects)}, indent=2) + '\n')
imports = set()
jobs = []
files = []
for label, folder, name, digest in specs:
    packet = base / folder
    raw = packet / name
    probes = packet / 'PROBES.lean.txt'
    assert hashlib.sha256(raw.read_bytes()).hexdigest() == digest
    assert probes.read_bytes().count(b'#print axioms ') == 1
    source = run / 'source/MicroCFTA' / name
    source.parent.mkdir(parents=True, exist_ok=True)
    source.write_bytes(raw.read_bytes() + b'\n' + probes.read_bytes())
    imports.update(line.split()[1] for line in raw.read_text().splitlines() if line.startswith('import '))
    command = 'exec lake env lean -j1 -DwarningAsError=true -R ' + shlex.quote(str(source.parent.parent))
    command += ' -o ' + shlex.quote(str(objects / (label + '.olean'))) + ' ' + shlex.quote(str(source))
    jobs.append((label, command, 1))
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
          'generic_lemmas_only': True, 'actual_source_dependency_cut_proved': False,
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
print(json.dumps({'run': str(run), 'objects': str(objects), 'module_reports': 3}))
