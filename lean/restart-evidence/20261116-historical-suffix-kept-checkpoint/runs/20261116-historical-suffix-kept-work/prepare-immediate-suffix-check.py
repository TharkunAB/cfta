from pathlib import Path
import hashlib
import json
import shlex
import tempfile

root = Path('/home/tritlo/Code/mcfta')
base = root / 'lean/restart-evidence'
run = base / '20261116-real-parked-immediate-suffix-kept-check'
run.mkdir()
packet = base / '20261116-real-parked-immediate-suffix-kept-draft'
for line in (packet / 'MANIFEST.sha256').read_text().splitlines():
    digest, name = line.split(None, 1)
    path = packet / name.strip().lstrip('*')
    assert hashlib.sha256(path.read_bytes()).hexdigest() == digest, path
append = (packet / 'APPEND.lean.txt').read_bytes()
assert hashlib.sha256(append).hexdigest() == 'c47d185496fe2342fd3b6de4876ca37c34a181d8ef3c5b3ff5219fd7c8683a85'
header = (packet / 'PRIVATE-HEADER.lean.txt').read_bytes()
assert hashlib.sha256(header).hexdigest() == '39c74198112999d58c4da79dcd03d5534ca23468864bcf6d03bd51bab741bd2c'
assert header.rstrip() + b' := by' in append
owner = root / 'lean/MicroCFTA/SourcePruningEnumerationSharedEagerReservation.lean'
published_pins = json.loads((base / '20261116-expanded-birth-and-actual-kept-publication/source-pins.json').read_text())
for name, digest in published_pins.items():
    if name.startswith('lean/MicroCFTA/') or name in ['shell.nix', 'lean/lean-toolchain', 'lean/lakefile.toml', 'lean/lake-manifest.json']:
        assert hashlib.sha256((root / name).read_bytes()).hexdigest() == digest, name
probes = (packet / 'PROBES.lean.txt').read_bytes()
assert probes.count(b'#print axioms ') == 1
raw = b'import MicroCFTA.SourcePruningEnumerationParkedRemovedBucketInputs\n' + owner.read_bytes() + b'\n' + append + b'\n' + probes
source = run / 'source/MicroCFTA' / owner.name
source.parent.mkdir(parents=True)
source.write_bytes(raw)
objects = Path(tempfile.mkdtemp(prefix='mcfta-real-parked-immediate-suffix-kept-'))
(run / 'objects.json').write_text(json.dumps({'path': str(objects)}, indent=2) + '\n')
imports = sorted({line.split()[1] for line in raw.decode().splitlines() if line.startswith('import ')})
command = 'exec lake env lean -j1 -DwarningAsError=true -R ' + shlex.quote(str(source.parent.parent))
command += ' -o ' + shlex.quote(str(objects / 'ImmediateSuffix.olean')) + ' ' + shlex.quote(str(source))
jobs = [('public-dependencies', 'exec lake build ' + ' '.join(imports), 0), ('real-parked-immediate-suffix-kept', command, 1)]
template = (base / '20261116-expanded-birth-and-actual-kept-publication/check.py').read_text()
driver = template[:template.index('\njobs =')]
driver += '\njobs = ' + repr(jobs) + '''
for name, command, count in jobs:
    run(name, command, count)
passed = [c['exit'] == 0 and not c['nonstandard_axioms'] and not c['diagnostics'] and not c['sorryAx']
          and (not job[2] or c['total_axiom_reports'] == job[2]) for c, job in zip(checks, jobs)]
report = {'checks': checks, 'passed': passed, 'source_pins_unchanged': True,
          'one_authentic_clear_event_same_output_kept_proved': all(passed),
          'every_historical_event_attached_proved': False,
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
(run / 'selection.json').write_text(json.dumps({'owner': str(owner.relative_to(root)), 'normal_extra_import': 'MicroCFTA.SourcePruningEnumerationParkedRemovedBucketInputs', 'packet': str(packet.relative_to(root)), 'append_sha256': hashlib.sha256(append).hexdigest(), 'header_sha256': hashlib.sha256(header).hexdigest(), 'reports': 1}, indent=2) + '\n')
print(json.dumps({'run': str(run), 'objects': str(objects), 'reports': 1}))
