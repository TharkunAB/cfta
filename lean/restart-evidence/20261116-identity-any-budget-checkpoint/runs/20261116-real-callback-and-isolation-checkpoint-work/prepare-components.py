from pathlib import Path
import hashlib
import json
import shlex
import tempfile

root = Path('/home/tritlo/Code/mcfta')
base = root / 'lean/restart-evidence'
run = base / '20261116-native-callback-and-isolation-repairs-check'
run.mkdir()
objects = Path(tempfile.mkdtemp(prefix='mcfta-real-components-'))
specs = [
    ('real-callback', '20261116-current-real-worker-callback-raw-membership-repair',
     'SourcePruningEnumerationRealWorkerCallbackResources.lean',
     'd1568491925808a952c69b4ff7826e624da3b0f65647f4f4bf6281874fb28a35'),
    ('earlier-isolation', '20261116-current-real-prefix-earlier-isolated-operational-repair',
     'SourcePruningEnumerationPrefixIsolatedAtOriginalBudget.lean',
     '74681daaa58f79a49a187fd3d3e4ca919c72d560d410511c08e69f0b9af52f14'),
]
pins = sorted((root / 'lean/MicroCFTA').glob('*.lean'))
pins += [root / name for name in ['shell.nix', 'lean/lean-toolchain', 'lean/lakefile.toml', 'lean/lake-manifest.json']]
pins.append(Path(__file__))
dependencies, components = set(), []
for label, folder, name, digest in specs:
    packet = base / folder
    raw, probe = packet / name, packet / 'PROBES.lean.txt'
    assert hashlib.sha256(raw.read_bytes()).hexdigest() == digest
    dependencies.update(line.split()[1] for line in raw.read_text().splitlines() if line.startswith('import '))
    source = run / (label + '-source') / 'MicroCFTA' / name
    source.parent.mkdir(parents=True)
    source.write_bytes(raw.read_bytes() + b'\n' + probe.read_bytes())
    command = 'exec lake env lean -j1 -DwarningAsError=true -R ' + shlex.quote(str(source.parent.parent))
    command += ' -o ' + shlex.quote(str(objects / (label + '.olean'))) + ' ' + shlex.quote(str(source))
    components.append((label, command, probe.read_text().count('#print axioms ')))
    pins += [raw, probe, source]
jobs = [('public-dependencies', 'exec lake build ' + ' '.join(shlex.quote(m) for m in sorted(dependencies)), 0)] + components
template = (base / '20261115-native-open-binder-helper-dependencies/check.py').read_text()
driver = template[:template.index('run("public-dependency"')]
driver += 'jobs = ' + repr(jobs) + '''
for name, command, count in jobs:
    try:
        run(name, command, count)
    except AssertionError:
        pass
assert all(item['exit'] == 0 and not item['nonstandard_axioms'] for item in checks)
(runtime / 'checked.json').write_text(json.dumps({'checks':checks,'source_pins_unchanged':True,
    'full_real_worker_proved':False,'joint_finite_completion_proved':False},indent=2)+'\\n')
'''
(run / 'check.py').write_text(driver)
pins.append(run / 'check.py')
(run / 'source-pins.json').write_text(json.dumps({str(p.relative_to(root)):hashlib.sha256(p.read_bytes()).hexdigest() for p in pins},indent=2)+'\n')
(run / 'objects.json').write_text(json.dumps({'path':str(objects)},indent=2)+'\n')
print(json.dumps({'run':str(run),'objects':str(objects),'jobs':[(name,count) for name,_,count in jobs]}))
