from pathlib import Path
import hashlib
import json
import shlex
import tempfile

root = Path('/home/tritlo/Code/mcfta')
base = root / 'lean/restart-evidence'
packet = base / '20261117-original-universe-optional-no-new-mu-trace-and-fields-repair'
run = base / '20261117-original-universe-optional-no-new-mu-trace-fields-check'
sha = lambda data: hashlib.sha256(data).hexdigest()
manifest = json.loads((packet / 'MANIFEST.json').read_text())
for name, pin in manifest['files'].items():
    data = (packet / name).read_bytes()
    assert sha(data) == pin['sha256'] and len(data) == pin['bytes'], name
layout = json.loads((packet / 'CHECK-LAYOUT.json').read_text())
owner = (root / layout['normal_owner']).read_bytes()
assert sha(owner) == layout['owner_sha256']
raw = (packet / 'IMPORTS.lean.txt').read_bytes() + owner + b'\n' + (packet / 'APPEND.lean.txt').read_bytes()
assert sha(raw) == layout['candidate_pure_source_sha256']
assert raw[55:55 + len(owner)] == owner
assert (packet / 'PUBLIC-DECLARATION.lean.txt').read_bytes() in raw
assert sha((packet / 'PUBLIC-HEADER.lean.txt').read_bytes()) == '441e737633652496ebc721725b1d9dbb10c80bceb3ee6efa8895e692c7cf9744'
assert b'set_option maxHeartbeats' not in raw
new_probes = (packet / 'PROBES.lean.txt').read_bytes()
assert sha(raw + b'\n' + new_probes) == layout['candidate_assembled_sha256']
old_probes = (base / '20261117-native-source-admission-publication/SourceSynthesisCurrentUniverseNativeAllocation-PROBES.lean.txt').read_bytes()
probes = old_probes + b'\n' + new_probes
assert probes.count(b'#print axioms ') == 43
run.mkdir()
source = run / 'source/MicroCFTA/SourceSynthesisCurrentUniverseNativeAllocation.lean'
source.parent.mkdir(parents=True)
source.write_bytes(raw + b'\n' + probes)
objects = Path(tempfile.mkdtemp(prefix='mcfta-causal-normal-module-'))
(run / 'objects.json').write_text(json.dumps({'path': str(objects)}, indent=2) + '\n')
imports = sorted({line.split()[1] for line in raw.decode().splitlines() if line.startswith('import ')})
command = 'exec lake env lean -j1 -DwarningAsError=true -R ' + shlex.quote(str(source.parent.parent))
command += ' -o ' + shlex.quote(str(objects / source.name.replace('.lean', '.olean'))) + ' ' + shlex.quote(str(source))
jobs = [('public-dependencies', 'exec lake build ' + ' '.join(imports), 0), ('normal-module', command, 43)]
previous = (base / '20261117-original-universe-optional-no-new-mu-layout-check/check.py').read_text()
head = previous[:previous.index('\njobs =')]
tail = previous[previous.index('\nfor name, command, count in jobs:'):]
(run / 'check.py').write_text(head + '\njobs = ' + repr(jobs) + tail)
selection = {'packet': packet.name, 'pure_source_sha256': sha(raw),
             'public441e_header_exact': True, 'old_owner_exact_offset': 55,
             'native363_reports': 37, 'new_optional441e_reports': 6,
             'total_reports': 43, 'normal_source_changed': False,
             'proof_limits': 'unchanged defaults', 'fuel_changes': False}
(run / 'selection.json').write_text(json.dumps(selection, indent=2) + '\n')
files = list((root / 'lean/MicroCFTA').glob('*.lean'))
files += [root / n for n in ['shell.nix', 'lean/lean-toolchain', 'lean/lakefile.toml', 'lean/lake-manifest.json']]
files += [p for p in packet.iterdir() if p.is_file()]
files += [Path(__file__), source, run / 'check.py', run / 'selection.json',
          base / '20261117-native-source-admission-publication/SourceSynthesisCurrentUniverseNativeAllocation-PROBES.lean.txt']
(run / 'source-pins.json').write_text(json.dumps({str(p.relative_to(root)): sha(p.read_bytes()) for p in files}, indent=2) + '\n')
print(json.dumps({'run': str(run), 'objects': str(objects), 'reports': 43, **selection}))
