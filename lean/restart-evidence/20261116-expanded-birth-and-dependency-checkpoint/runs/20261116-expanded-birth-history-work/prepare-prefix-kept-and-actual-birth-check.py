from pathlib import Path
import hashlib
import json
import shlex
import tempfile

root = Path('/home/tritlo/Code/mcfta')
base = root / 'lean/restart-evidence'
run = base / '20261116-prefix-kept-set-and-actual-birth-check'
run.mkdir()
owner = root / 'lean/MicroCFTA/SourcePruningEnumerationSharedEagerReservation.lean'
assert hashlib.sha256(owner.read_bytes()).hexdigest() == 'd4dba9e0a86c4b5fe8d69e379aebe4614da5bb99d8d1d1bfe7c87e4544fe94e6'
prefix = base / '20261116-prefix-expanded-birth-history-draft'
kept = base / '20261116-expanded-birth-direct-kept-set-draft'
appendices = [
    ('20261116-actual-own-expanded-birth-history-draft', '4c360c83bb7d7396f800c99bddef00be27428bbca7e4ba7c70500aa2f6c93cb8'),
    ('20261116-actual-child-finalizer-expanded-birth-history-draft', 'bc563df1a10fbf6a98ed59a933d9d970d649978e173a1e564bb7a0b5478ed51b'),
    ('20261116-actual-tuple-finalizer-expanded-birth-history-draft', 'b9df7ec9b54bbc33a9f3cf7f1120d58669f760d24a07f21daed43fe78ee7dc2a'),
]
raw_owner = b'import MicroCFTA.EnumerationExpandedBirthHistory\n' + owner.read_bytes()
owner_probes = b''
files = []
for folder, digest in appendices:
    packet = base / folder
    raw = (packet / 'APPEND.lean.txt').read_bytes()
    assert hashlib.sha256(raw).hexdigest() == digest
    raw_owner += b'\n' + raw
    owner_probes += b'\n' + (packet / 'PROBES.lean.txt').read_bytes()
    files.extend(p for p in packet.iterdir() if p.is_file())
assert hashlib.sha256((prefix / 'SourcePruningEnumerationPrefixExpandedBirthHistory.lean').read_bytes()).hexdigest() == '9fcaf9929fe69cb7caf92b81a37400ddf7eab129eb203f9a19f07c4a4d6ae65d'
assert hashlib.sha256((kept / 'EnumerationExpandedBirthKeptSet.lean').read_bytes()).hexdigest() == '6c8e54f1a8e452bab19a9e86644111dba1a8ed02e1ae57cc2c99579ea7bfec25'
specs = [
    ('actual-prefix-birth', 'SourcePruningEnumerationPrefixExpandedBirthHistory.lean',
     (prefix / 'SourcePruningEnumerationPrefixExpandedBirthHistory.lean').read_bytes(),
     (prefix / 'PROBES.lean.txt').read_bytes(), 1),
    ('direct-kept-set', 'EnumerationExpandedBirthKeptSet.lean',
     (kept / 'EnumerationExpandedBirthKeptSet.lean').read_bytes(),
     (kept / 'PROBES.lean.txt').read_bytes(), 2),
    ('actual-own-child-and-tuple-birth', owner.name, raw_owner, owner_probes, 3),
]
objects = Path(tempfile.mkdtemp(prefix='mcfta-prefix-kept-actual-birth-'))
(run / 'objects.json').write_text(json.dumps({'path': str(objects)}, indent=2) + '\n')
imports = set()
jobs = []
files += [p for folder in [prefix, kept] for p in folder.iterdir() if p.is_file()]
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
template = (base / '20261116-expanded-birth-history-typed-definition-check/check.py').read_text()
driver = template[:template.index('\njobs =')]
driver += '\njobs = ' + repr(jobs) + '''
for name, command, count in jobs:
    run(name, command, count)
passed = [c['exit'] == 0 and not c['nonstandard_axioms'] and not c['diagnostics'] and not c['sorryAx'] and (not job[2] or c['total_axiom_reports'] == job[2])
          for c, job in zip(checks, jobs)]
report = {'checks': checks, 'passed': passed, 'source_pins_unchanged': True,
          'prefix_kept_set_and_local_actual_birth_only': True,
          'whole_worker_strong_birth_proved': False, 'joint_finite_completion_proved': False,
          'haskell_changed': False, 'limits': limits}
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
print(json.dumps({'run': str(run), 'objects': str(objects), 'reports': 6}))
