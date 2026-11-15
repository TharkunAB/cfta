from pathlib import Path
import argparse
import hashlib
import json
import shlex
import tempfile

root = Path('/home/tritlo/Code/mcfta')
base = root / 'lean/restart-evidence'
parser = argparse.ArgumentParser()
parser.add_argument('--run', required=True)
parser.add_argument('--spec', action='append', default=[])
parser.add_argument('--example', action='append', default=[])
parser.add_argument('--build', action='append', default=[])
args = parser.parse_args()
runtime = base / args.run
runtime.mkdir()
source_root = runtime / 'source'
(source_root / 'MicroCFTA').mkdir(parents=True)
objects = Path(tempfile.mkdtemp(prefix='mcfta-private-proof-')) / 'objects/MicroCFTA'
objects.mkdir(parents=True)
pins = sorted((root / 'lean/MicroCFTA').glob('*.lean'))
pins += [root / name for name in ['shell.nix', 'lean/lean-toolchain', 'lean/lakefile.toml', 'lean/lake-manifest.json']]
pins.append(Path(__file__))
jobs = []
if args.build:
    jobs.append(('public-dependencies', 'exec lake build ' + ' '.join(shlex.quote(name) for name in args.build), 0))
for spec in args.spec:
    folder, module = spec.rsplit(':', 1)
    draft = base / folder
    raw = draft / (module + '.lean')
    probe = draft / 'PROBES.lean.txt'
    content = '\n'.join(line for line in probe.read_text().splitlines()
                        if not line.startswith('import MicroCFTA.' + module))
    source = source_root / 'MicroCFTA' / raw.name
    source.write_text(raw.read_text() + '\n' + content + '\n')
    command = 'exec lake env lean -j1 -DwarningAsError=true -R ' + shlex.quote(str(source_root))
    command += ' -o ' + shlex.quote(str(objects / (module + '.olean'))) + ' ' + shlex.quote(str(source))
    jobs.append((module, command, 1))
    pins += [raw, probe, source]
for name in args.example:
    source = base / name
    jobs.append((source.stem, 'exec lake env lean -j1 -DwarningAsError=true ' + shlex.quote(str(source)), 0))
    pins.append(source)
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
    'whole_native_history_returned_footprint_proved':False},indent=2)+'\\n')
'''
(runtime / 'check.py').write_text(driver)
pins.append(runtime / 'check.py')
(runtime / 'source-pins.json').write_text(json.dumps({str(path.relative_to(root)): hashlib.sha256(path.read_bytes()).hexdigest()
                                                    for path in pins}, indent=2) + '\n')
print(json.dumps({'run':str(runtime),'objects':str(objects),'pins':len(pins),'jobs':len(jobs)}))
