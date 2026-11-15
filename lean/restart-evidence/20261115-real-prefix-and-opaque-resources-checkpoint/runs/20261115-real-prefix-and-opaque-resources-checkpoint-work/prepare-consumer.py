from pathlib import Path
import argparse
import hashlib
import json
import shlex
import tempfile

root = Path('/home/tritlo/Code/mcfta')
base = root / 'lean/restart-evidence'
work = Path(__file__).parent
parser = argparse.ArgumentParser()
parser.add_argument('--run', required=True)
parser.add_argument('--spec', action='append', required=True,
                    help='packet:append-file:probe-file')
parser.add_argument('--dependency-imports', type=Path)
args = parser.parse_args()
runtime = base / args.run
runtime.mkdir()
original = root / 'lean/MicroCFTA/SourcePruningEnumerationSharedEagerReservation.lean'
snapshot = original.read_bytes()
extra = args.dependency_imports.read_bytes() if args.dependency_imports else b''
modules = [line.split()[1] for line in extra.decode().splitlines() if line.startswith('import ')]
assert all(not line.strip() or line.startswith('import MicroCFTA.') for line in extra.decode().splitlines())
baseline = (root / 'lean/restart-evidence/20261115-actual-source-resource-induction-checkpoint-work/BASE-SOURCE.lean.txt').read_bytes()
position = snapshot.index(baseline)
assert all(not line.strip() or line.startswith(b'import MicroCFTA.') for line in snapshot[:position].splitlines())
objects = Path(tempfile.mkdtemp(prefix='mcfta-private-proof-')) / 'objects/MicroCFTA'
objects.mkdir(parents=True)
pins = sorted((root / 'lean/MicroCFTA').glob('*.lean'))
pins += [root / name for name in ['shell.nix', 'lean/lean-toolchain', 'lean/lakefile.toml', 'lean/lake-manifest.json']]
pins += [Path(__file__), root / 'lean/restart-evidence/20261115-actual-source-resource-induction-checkpoint-work/BASE-SOURCE.lean.txt']
jobs = [('public-dependencies', 'exec lake build MicroCFTA.SourcePruningEnumerationSharedEagerReservation' + ''.join(' ' + shlex.quote(name) for name in modules), 0)]
if args.dependency_imports:
    pins.append(args.dependency_imports.resolve())
for index, spec in enumerate(args.spec):
    folder, name, probe_name = spec.split(':')
    draft = base / folder
    raw, probe = draft / name, draft / probe_name
    assert not any(line.startswith('import ') for line in raw.read_text().splitlines())
    assert not any(line.startswith('import ') for line in probe.read_text().splitlines())
    source_root = runtime / ('candidate-' + str(index))
    source = source_root / 'MicroCFTA' / original.name
    source.parent.mkdir(parents=True)
    source.write_bytes(extra + b'\n' + snapshot + b'\n' + raw.read_bytes() + b'\n' + probe.read_bytes() + b'\n')
    output = objects / ('candidate-' + str(index)) / (original.stem + '.olean')
    output.parent.mkdir()
    command = 'exec lake env lean -j1 -DwarningAsError=true -R ' + shlex.quote(str(source_root))
    command += ' -o ' + shlex.quote(str(output)) + ' ' + shlex.quote(str(source))
    jobs.append((folder, command, probe.read_text().count('#print axioms ')))
    pins += [raw, probe, source]
template = (base / '20261115-native-open-binder-helper-dependencies/check.py').read_text()
driver = template[:template.index('run("public-dependency"')]
driver += 'jobs = ' + repr(jobs) + '\n'
driver += '''for name, command, count in jobs:
    try:
        run(name, command, count)
    except AssertionError:
        pass
assert all(item['exit'] == 0 and not item['nonstandard_axioms'] for item in checks)
(runtime/'checked.json').write_text(json.dumps({'checks':checks,'source_pins_unchanged':True,
    'original_prepared_scan_all_66_resources_proved':False,
    'full_source_worker_and_joint_finite_completion_proved':False},indent=2)+'\\n')
'''
(runtime / 'check.py').write_text(driver)
pins.append(runtime / 'check.py')
(runtime / 'source-pins.json').write_text(json.dumps({str(path.relative_to(root)): hashlib.sha256(path.read_bytes()).hexdigest()
                                                    for path in pins}, indent=2) + '\n')
(runtime / 'base-source.sha256').write_text(hashlib.sha256(snapshot).hexdigest() + '\n')
print(json.dumps({'run': str(runtime), 'objects': str(objects), 'pins': len(pins), 'jobs': len(jobs)}))
