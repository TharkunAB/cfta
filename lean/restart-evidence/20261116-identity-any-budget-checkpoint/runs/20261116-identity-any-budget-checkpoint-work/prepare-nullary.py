from pathlib import Path
import hashlib
import json
import shlex
import tempfile

root = Path('/home/tritlo/Code/mcfta')
base = root / 'lean/restart-evidence'
run = base / '20261116-native-real-nullary-constructor-check'
run.mkdir()
objects = Path(tempfile.mkdtemp(prefix='mcfta-real-nullary-'))
packet = base / '20261116-current-real-nullary-captured-frame-constructor-repair'
raw = packet / 'SourcePruningEnumerationRealNullaryCapturedFrameResources.lean'
probe = packet / 'PROBES.lean.txt'
assert hashlib.sha256(raw.read_bytes()).hexdigest() == 'b9d3ec419bff238057ef1fefad72dbccb93fa5f2281b29756401549589ec2512'
source = run / 'source/MicroCFTA' / raw.name
source.parent.mkdir(parents=True)
source.write_bytes(raw.read_bytes() + b'\n' + probe.read_bytes())
dependencies = sorted({line.split()[1] for line in raw.read_text().splitlines() if line.startswith('import ')})
command = 'exec lake env lean -j1 -DwarningAsError=true -R ' + shlex.quote(str(source.parent.parent))
command += ' -o ' + shlex.quote(str(objects / 'Nullary.olean')) + ' ' + shlex.quote(str(source))
jobs = [('public-dependencies', 'exec lake build ' + ' '.join(shlex.quote(m) for m in dependencies), 0),
    ('real-nullary-captured-frame', command, probe.read_text().count('#print axioms '))]
template = (base / '20261115-native-open-binder-helper-dependencies/check.py').read_text()
driver = template[:template.index('run("public-dependency"')]
driver += 'jobs = ' + repr(jobs) + '''
for name, command, count in jobs:
    run(name, command, count)
(runtime / 'checked.json').write_text(json.dumps({'checks':checks,'source_pins_unchanged':True,
    'nullary_actual_captured_frame_proved':True,'whole_real_worker_proved':False,
    'joint_finite_completion_proved':False},indent=2)+'\\n')
'''
(run / 'check.py').write_text(driver)
pins = sorted((root / 'lean/MicroCFTA').glob('*.lean'))
pins += [root / n for n in ['shell.nix','lean/lean-toolchain','lean/lakefile.toml','lean/lake-manifest.json']]
pins += [raw,probe,source,run / 'check.py',Path(__file__)]
(run / 'source-pins.json').write_text(json.dumps({str(p.relative_to(root)):hashlib.sha256(p.read_bytes()).hexdigest() for p in pins},indent=2)+'\n')
(run / 'objects.json').write_text(json.dumps({'path':str(objects)},indent=2)+'\n')
print(json.dumps({'run':str(run),'objects':str(objects),'reports':jobs[-1][2]}))
