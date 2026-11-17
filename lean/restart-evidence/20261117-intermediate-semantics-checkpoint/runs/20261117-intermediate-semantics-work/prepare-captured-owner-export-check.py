from pathlib import Path
import hashlib
import json
import shlex
import tempfile

root = Path('/home/tritlo/Code/mcfta')
base = root / 'lean/restart-evidence'
packet = base / '20261117-captured-current-resource-export-context-repair'
runtime = base / '20261117-captured-current-owner-export-check'
owner = root / 'lean/MicroCFTA/SourcePruningEnumerationSharedEagerReservation.lean'
sha = lambda data: hashlib.sha256(data).hexdigest()
manifest = json.loads((packet / 'MANIFEST.json').read_text())
for name, entry in manifest['files'].items():
    data = (packet / name).read_bytes()
    assert sha(data) == (entry['sha256'] if isinstance(entry, dict) else entry), name
assembly = json.loads((packet / 'ASSEMBLY.json').read_text())
old = owner.read_bytes()
assert len(old) == assembly['base_bytes'] and sha(old) == assembly['base_sha256']
append = (packet / 'APPEND.lean.txt').read_bytes()
assert sha(append) == assembly['append_sha256']
assert append.count(b'set_option maxHeartbeats') == 1
assert b'set_option maxHeartbeats 200000 in' in append
assembled = old + append
assert assembled.startswith(old)
assert sha(assembled) == assembly['expected_assembled_sha256']
old_probes = (base / '20261117-source-demand-causal-publication/ResourceProbes208.lean.txt').read_bytes()
new_probes = (packet / 'PROBES.lean.txt').read_bytes()
assert old_probes.count(b'#print axioms ') == 208
assert new_probes.count(b'#print axioms ') == 1
runtime.mkdir()
source = runtime / 'source/MicroCFTA' / owner.name
source.parent.mkdir(parents=True)
source.write_bytes(assembled + b'\n' + old_probes + b'\n' + new_probes)
(runtime / 'OWNER-BEFORE.lean.txt').write_bytes(old)
(runtime / 'APPEND.lean.txt').write_bytes(append)
(runtime / 'ASSEMBLY.json').write_text(json.dumps(assembly, indent=2) + '\n')
objects = Path(tempfile.mkdtemp(prefix='mcfta-captured-owner-export-'))
(runtime / 'objects.json').write_text(json.dumps({'path': str(objects)}, indent=2) + '\n')
imports = sorted({line.split()[1] for line in old.decode().splitlines() if line.startswith('import ')})
command = 'exec lake env lean -j1 -DwarningAsError=true -R ' + shlex.quote(str(source.parent.parent))
command += ' -o ' + shlex.quote(str(objects / 'SourcePruningEnumerationSharedEagerReservation.olean'))
command += ' ' + shlex.quote(str(source))
jobs = [('public-dependencies', 'exec lake build ' + ' '.join(imports), 0),
        ('owner-and-append', command, 209)]
template = (base / '20261117-top-arrow-staged-input-empty-append-check/check.py').read_text()
driver = template[:template.index('\njobs =')]
driver += '\njobs = ' + repr(jobs) + '''
for name, command, count in jobs:
    run(name, command, count)
passed = [c['exit'] == 0 and not c['nonstandard_axioms'] and not c['diagnostics'] and not c['sorryAx']
          and (not job[2] or c['total_axiom_reports'] == job[2]) for c, job in zip(checks, jobs)]
report = {'checks': checks, 'passed': passed, 'source_pins_unchanged': True,
          'normal_module_checked': all(passed), 'old_owner_exact_prefix': True,
          'old_owner_proof_limits_unchanged': True, 'new_export_maxHeartbeats': 200000,
          'owner_resource_probes': 208, 'new_theorem_reports': 1, 'new_declaration_checks': 1,
          'same_actual_tuple_selected_finalized_callback_packets_proved': all(passed),
          'actual_completed_tuple_current_produced': False,
          'joint_finite_completion_proved': False, 'haskell_changed': False, 'limits': limits}
(runtime / 'results.json').write_text(json.dumps(report, indent=2) + '\\n')
assert len(checks) == 2 and all(passed)
(runtime / 'checked.json').write_text(json.dumps(report, indent=2) + '\\n')
print(json.dumps(report), flush=True)
'''
(runtime / 'check.py').write_text(driver)
selection = {'packet': packet.name, 'owner': str(owner.relative_to(root)),
    'assembled_sha256': sha(assembled), 'old_owner_sha256': sha(old),
    'old_owner_bytes': len(old), 'append_sha256': sha(append), 'reports': 209,
    'normal_imports_only': True, 'old_owner_exact_prefix': True}
(runtime / 'selection.json').write_text(json.dumps(selection, indent=2) + '\n')
files = list((root / 'lean/MicroCFTA').glob('*.lean'))
files += [root / name for name in ['shell.nix', 'lean/lean-toolchain', 'lean/lakefile.toml', 'lean/lake-manifest.json']]
files += [path for path in packet.iterdir() if path.is_file()]
files += [path for path in runtime.iterdir() if path.is_file()]
files += [source, Path(__file__)]
(runtime / 'source-pins.json').write_text(json.dumps({str(path.relative_to(root)): sha(path.read_bytes())
    for path in files}, indent=2) + '\n')
print(json.dumps({'run': str(runtime), 'objects': str(objects), 'reports': 209,
                  'old_owner_bytes_preserved': len(old), 'new_export_default_heartbeats': 200000}))
