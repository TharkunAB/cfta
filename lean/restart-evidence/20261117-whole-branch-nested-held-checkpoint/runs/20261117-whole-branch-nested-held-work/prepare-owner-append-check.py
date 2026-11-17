from pathlib import Path
import hashlib
import json
import re
import shlex
import sys
import tempfile

root = Path('/home/tritlo/Code/mcfta')
base = root / 'lean/restart-evidence'
work = Path(__file__).parent
run_name, imports_arg, *packet_names = sys.argv[1:]
assert re.fullmatch(r'2026[0-9]{4}-[a-z0-9-]+', run_name)
assert packet_names
sha = lambda data: hashlib.sha256(data).hexdigest()
owner = root / 'lean/MicroCFTA/SourcePruningEnumerationSharedEagerReservation.lean'
original = owner.read_bytes()
assert sha(original) == '25a69789eb205f5c0787902786114b3cead00f30ad8f8570b3e6d51a7f84f8fc'
imports = [] if imports_arg == '-' else imports_arg.split(',')
assert all(re.fullmatch(r'MicroCFTA\.[A-Za-z0-9_.]+', name) for name in imports)
prefix = ''.join('import ' + name + '\n' for name in imports).encode()
append = b''
new_probes = b''
packet_files = []
for name in packet_names:
    assert re.fullmatch(r'2026[0-9]{4}-[a-z0-9-]+', name)
    packet = base / name
    if (packet / 'MANIFEST.sha256').exists():
        for line in (packet / 'MANIFEST.sha256').read_text().splitlines():
            digest, file_name = line.split(None, 1)
            assert sha((packet / file_name.strip().lstrip('*')).read_bytes()) == digest
    else:
        manifest = json.loads((packet / 'MANIFEST.json').read_text())
        files = manifest.get('files', manifest)
        entries = ((item['path'], item) for item in files) if isinstance(files, list) else files.items()
        for file_name, item in entries:
            digest = item['sha256'] if isinstance(item, dict) else item
            data = (packet / file_name).read_bytes()
            assert sha(data) == digest, file_name
            if isinstance(item, dict):
                assert len(data) == item['bytes'], file_name
    raw = (packet / 'APPEND.lean.txt').read_bytes()
    assert all(line.strip() == b'set_option maxHeartbeats 200000'
               for line in raw.splitlines() if b'set_option maxHeartbeats' in line)
    append += b'\n' + raw
    new_probes += b'\n' + (packet / 'PROBES.lean.txt').read_bytes()
    packet_files += [p for p in packet.iterdir() if p.is_file()]
old_probes = (work / 'PreviousOwnerProbes235.lean.txt').read_bytes()
assert old_probes.count(b'#print axioms ') == 235
count = 235 + new_probes.count(b'#print axioms ')
run = base / run_name
run.mkdir()
source = run / 'source/MicroCFTA/SourcePruningEnumerationSharedEagerReservation.lean'
source.parent.mkdir(parents=True)
assembled = prefix + original + append
assert assembled[len(prefix):len(prefix) + len(original)] == original
source.write_bytes(assembled + b'\n' + old_probes + new_probes)
objects = Path(tempfile.mkdtemp(prefix='mcfta-nested-held-owner-'))
(run / 'objects.json').write_text(json.dumps({'path': str(objects)}, indent=2) + '\n')
dependencies = sorted({line.split()[1] for line in assembled.decode().splitlines()
                       if line.startswith('import ')})
jobs = [('public-dependencies', 'exec lake build ' + ' '.join(dependencies), 0),
        ('owner-and-appends', 'exec lake env lean -j1 -DwarningAsError=true -R '
         + shlex.quote(str(source.parent.parent)) + ' -o '
         + shlex.quote(str(objects / 'SourcePruningEnumerationSharedEagerReservation.olean'))
         + ' ' + shlex.quote(str(source)), count)]
template = (base / '20261117-literal-current-combined-check/check.py').read_text()
driver = template[:template.index('\njobs =')]
driver += '\njobs = ' + repr(jobs) + '''
for name, command, count in jobs:
    run(name, command, count)
passed = [c['exit'] == 0 and not c['nonstandard_axioms'] and not c['diagnostics'] and not c['sorryAx']
          and (not job[2] or c['total_axiom_reports'] == job[2]) for c, job in zip(checks, jobs)]
report = {'checks': checks, 'passed': passed, 'source_pins_unchanged': True,
          'owner_append_checked': all(passed), 'old_owner_entire_exact_contiguous_block': True,
          'old_owner_proof_bodies_and_limits_unchanged': True,
          'new_proof_maxHeartbeats': 200000, 'joint_finite_completion_proved': False,
          'haskell_changed': False, 'limits': limits}
(runtime / 'results.json').write_text(json.dumps(report, indent=2) + '\\n')
assert len(checks) == 2 and all(passed)
(runtime / 'checked.json').write_text(json.dumps(report, indent=2) + '\\n')
print(json.dumps(report), flush=True)
'''
(run / 'check.py').write_text(driver)
selection = {'packets': packet_names, 'owner': str(owner.relative_to(root)),
             'old_owner_sha256': sha(original), 'old_owner_bytes': len(original),
             'old_owner_offset': len(prefix), 'import_prefix_sha256': sha(prefix),
             'append_sha256': sha(append), 'assembled_sha256': sha(assembled),
             'previous_owner_reports': 235, 'reports': count,
             'new_private_reports': new_probes.count(b'#print axioms '),
             'runtime_fuels_unchanged': True, 'old_owner_entire_exact_contiguous_block': True,
             'all_new_proofs_maxHeartbeats': 200000}
(run / 'selection.json').write_text(json.dumps(selection, indent=2) + '\n')
files = list((root / 'lean/MicroCFTA').glob('*.lean'))
files += [root / name for name in ['shell.nix', 'lean/lean-toolchain', 'lean/lakefile.toml', 'lean/lake-manifest.json']]
files += packet_files + [Path(__file__), work / 'PreviousOwnerProbes235.lean.txt',
                          source, run / 'check.py', run / 'selection.json']
(run / 'source-pins.json').write_text(json.dumps({str(p.relative_to(root)): sha(p.read_bytes())
                                               for p in files}, indent=2) + '\n')
print(json.dumps({'run': str(run), 'objects': str(objects), 'reports': count,
                  'assembled_sha256': sha(assembled)}))
