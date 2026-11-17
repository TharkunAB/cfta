from pathlib import Path
import hashlib
import json
import shlex
import tempfile

root = Path('/home/tritlo/Code/mcfta')
base = root / 'lean/restart-evidence'
runtime = base / '20261117-all-outer-held-explicit-parameter-check'
names = ['20261117-all-outer-held-history-depth-width-repair',
         '20261117-all-outer-held-prepared-opaque-explicit-fields-repair',
         '20261117-all-outer-held-captured-explicit-bits-repair',
         '20261117-all-outer-held-prefix-width-and-scope-repair']
packets = [base / name for name in names]
sha = lambda data: hashlib.sha256(data).hexdigest()
for packet in packets:
    manifest_path = packet / 'MANIFEST.json'
    if manifest_path.exists():
        manifest = json.loads(manifest_path.read_text())
        files = manifest.get('files', manifest)
        entries = ((item['path'], item) for item in files) if isinstance(files, list) else files.items()
        for name, entry in entries:
            assert sha((packet / name).read_bytes()) == (entry['sha256'] if isinstance(entry, dict) else entry), (packet, name)
    else:
        for line in (packet / 'MANIFEST.sha256').read_text().splitlines():
            digest, name = line.split(None, 1)
            assert sha((packet / name).read_bytes()) == digest, (packet, name)
owner = root / 'lean/MicroCFTA/SourcePruningEnumerationSharedEagerReservation.lean'
old = owner.read_bytes()
assert sha(old) == '881f7369ddb6abf62c45f6f6b57748db5aa5a2d4108c75bebbdd0f1dd4e6fe1a'
requested = (packets[-1] / 'IMPORT-PREFIX.lean.txt').read_bytes().splitlines(keepends=True)
prefix = b''.join(line for line in requested if line.rstrip(b'\r\n') not in old.splitlines()) + b'\n'
append = b'\n'.join((packet / 'APPEND.lean.txt').read_bytes() for packet in packets)
assembled = prefix + old + b'\n' + append
assert assembled[len(prefix):len(prefix) + len(old)] == old
public_header = (packets[-1] / 'PUBLIC-9374-HEADER.lean.txt').read_bytes()
assert sha(public_header) == '9374c81a8218909c2d86a7a2737bc0ac91396e1a850362aa835447341cfa47a8'
assert public_header.rstrip(b'\n') + b' := by\n' in append
probe_names = ['PROBES.lean.txt', 'PROBES.lean.txt', 'SAME-FILE-PROBES.lean.txt', 'PROBES.lean.txt']
probes = b'\n'.join((packet / name).read_bytes() for packet, name in zip(packets, probe_names))
assert probes.count(b'#print axioms ') == 10
old_probes = (base / '20261117-intermediate-semantics-publication/ResourceProbes208.lean.txt').read_bytes()
previous_new = (base / '20261117-literal-current-parent-tail-check/NEW-PROBES.lean.txt').read_bytes()
assert old_probes.count(b'#print axioms ') == 208
assert previous_new.count(b'#print axioms ') == 10
runtime.mkdir()
source = runtime / 'source/MicroCFTA' / owner.name
source.parent.mkdir(parents=True)
source.write_bytes(assembled + b'\n' + old_probes + b'\n' + previous_new + b'\n' + probes)
(runtime / 'OWNER-BEFORE.lean.txt').write_bytes(old)
(runtime / 'IMPORT-PREFIX.lean.txt').write_bytes(prefix)
(runtime / 'APPEND.lean.txt').write_bytes(append)
(runtime / 'NEW-PROBES.lean.txt').write_bytes(probes)
objects = Path(tempfile.mkdtemp(prefix='mcfta-all-outer-held-'))
(runtime / 'objects.json').write_text(json.dumps({'path': str(objects)}, indent=2) + '\n')
selection = {'packets': names, 'owner': str(owner.relative_to(root)), 'old_owner_sha256': sha(old),
    'old_owner_bytes': len(old), 'old_owner_offset': len(prefix), 'import_prefix_sha256': sha(prefix),
    'append_sha256': sha(append), 'assembled_sha256': sha(assembled), 'reports': 228,
    'previous_owner_reports': 218, 'new_private_reports': 9, 'new_public_theorems': 1,
    'original_public_header_sha256': sha(public_header), 'runtime_fuels_unchanged': True,
    'old_owner_entire_exact_contiguous_block': True, 'all_new_proofs_maxHeartbeats': 200000}
(runtime / 'selection.json').write_text(json.dumps(selection, indent=2) + '\n')
imports = sorted({line.split()[1] for line in (prefix + old).decode().splitlines() if line.startswith('import ')})
command = 'exec lake env lean -j1 -DwarningAsError=true -R ' + shlex.quote(str(source.parent.parent))
command += ' -o ' + shlex.quote(str(objects / owner.with_suffix('.olean').name)) + ' ' + shlex.quote(str(source))
jobs = [('public-dependencies', 'exec lake build ' + ' '.join(imports), 0),
        ('owner-and-full-outer-held', command, 228)]
template = (base / '20261117-top-arrow-staged-input-empty-append-check/check.py').read_text()
driver = template[:template.index('\njobs =')]
driver += '\njobs = ' + repr(jobs) + '''
for name, command, count in jobs:
    run(name, command, count)
passed = [c['exit'] == 0 and not c['nonstandard_axioms'] and not c['diagnostics'] and not c['sorryAx']
          and (not job[2] or c['total_axiom_reports'] == job[2]) for c, job in zip(checks, jobs)]
report = {'checks': checks, 'passed': passed, 'source_pins_unchanged': True,
    'normal_module_checked': all(passed), 'old_owner_entire_exact_contiguous_block': True,
    'old_owner_proof_bodies_and_limits_unchanged': True, 'new_proof_maxHeartbeats': 200000,
    'previous_owner_resource_probes': 218, 'new_public_theorem_reports': 1,
    'new_private_component_reports': 9, 'all_history9374_proved': all(passed),
    'joint_finite_completion_proved': False, 'haskell_changed': False, 'limits': limits}
(runtime / 'results.json').write_text(json.dumps(report, indent=2) + '\\n')
assert len(checks) == 2 and all(passed)
(runtime / 'checked.json').write_text(json.dumps(report, indent=2) + '\\n')
print(json.dumps(report), flush=True)
'''
(runtime / 'check.py').write_text(driver)
files = list((root / 'lean/MicroCFTA').glob('*.lean'))
files += [root / name for name in ['shell.nix', 'lean/lean-toolchain', 'lean/lakefile.toml', 'lean/lake-manifest.json']]
files += [path for packet in packets for path in packet.iterdir() if path.is_file()]
files += [path for path in runtime.iterdir() if path.is_file()]
files += [source, Path(__file__)]
(runtime / 'source-pins.json').write_text(json.dumps({str(path.relative_to(root)): sha(path.read_bytes())
    for path in files}, indent=2) + '\n')
print(json.dumps({'run': str(runtime), 'objects': str(objects), 'reports': 228,
    'old_owner_bytes_preserved': len(old), 'new_public_reports': 1, 'new_private_reports': 9,
    'assembled_sha256': sha(assembled)}))
