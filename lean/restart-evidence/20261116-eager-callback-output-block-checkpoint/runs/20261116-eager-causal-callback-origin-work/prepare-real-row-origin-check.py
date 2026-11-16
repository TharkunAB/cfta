from pathlib import Path
import hashlib
import json
import shlex
import tempfile

root = Path('/home/tritlo/Code/mcfta')
base = root / 'lean/restart-evidence'
run = base / '20261116-real-eager-captured-row-origin-check'
run.mkdir()
packet = base / '20261116-real-eager-captured-output-causal-origin-draft'
manifest = json.loads((packet / 'MANIFEST.json').read_text())
for name, digest in manifest['files'].items():
    assert hashlib.sha256((packet / name).read_bytes()).hexdigest() == digest, name
name = 'SourcePruningEnumerationRealEagerCapturedOutputOrigin.lean'
raw = (packet / name).read_bytes()
assert hashlib.sha256(raw).hexdigest() == '2d6af45be459a32b2c594b6ef7428d9a89374c30583f523780d091206f02fc51'
header = (packet / 'PUBLIC-HEADER.lean.txt').read_bytes()
assert hashlib.sha256(header).hexdigest() == 'a363e9be78ea59a7511c40f8875662875f58a221afe309dae95f08ab2f1dcd31'
assert header.rstrip() + b' := by' in raw
probes = (packet / 'PROBES.lean.txt').read_bytes()
assert probes.count(b'#print axioms ') == 1
source = run / 'source/MicroCFTA' / name
source.parent.mkdir(parents=True)
source.write_bytes(raw + b'\n' + probes)
objects = Path(tempfile.mkdtemp(prefix='mcfta-real-eager-row-origin-'))
(run / 'objects.json').write_text(json.dumps({'path': str(objects)}, indent=2) + '\n')
imports = sorted({line.split()[1] for line in raw.decode().splitlines() if line.startswith('import ')})
command = 'exec lake env lean -j1 -DwarningAsError=true -R ' + shlex.quote(str(source.parent.parent))
command += ' -o ' + shlex.quote(str(objects / 'RowOrigin.olean')) + ' ' + shlex.quote(str(source))
jobs = [('public-dependencies', 'exec lake build ' + ' '.join(imports), 0), ('real-eager-captured-row-origin', command, 1)]
template = (base / '20261116-immediate-historical-suffix-kept-publication/check.py').read_text()
driver = template[:template.index('\njobs =')]
driver += '\njobs = ' + repr(jobs) + '''
for name, command, count in jobs:
    run(name, command, count)
passed = [c['exit'] == 0 and not c['nonstandard_axioms'] and not c['diagnostics'] and not c['sorryAx']
          and (not job[2] or c['total_axiom_reports'] == job[2]) for c, job in zip(checks, jobs)]
report = {'checks': checks, 'passed': passed, 'source_pins_unchanged': True,
          'actual_indexed_real_eager_row_origin_proved': all(passed),
          'literal_eager_callback_restart_origin_proved': False,
          'every_causal_historical_event_attached_proved': False,
          'joint_finite_completion_proved': False, 'haskell_changed': False, 'limits': limits}
(runtime / 'results.json').write_text(json.dumps(report, indent=2) + '\\n')
assert len(checks) == 2 and all(passed)
(runtime / 'checked.json').write_text(json.dumps(report, indent=2) + '\\n')
print(json.dumps(report), flush=True)
'''
(run / 'check.py').write_text(driver)
files = list((root / 'lean/MicroCFTA').glob('*.lean'))
files += [root / n for n in ['shell.nix', 'lean/lean-toolchain', 'lean/lakefile.toml', 'lean/lake-manifest.json']]
files += [p for p in packet.iterdir() if p.is_file()]
files += [Path(__file__), source, run / 'check.py']
(run / 'source-pins.json').write_text(json.dumps({str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest() for p in files}, indent=2) + '\n')
print(json.dumps({'run': str(run), 'objects': str(objects), 'reports': 1, 'proof_limit': 'unchanged default'}))
