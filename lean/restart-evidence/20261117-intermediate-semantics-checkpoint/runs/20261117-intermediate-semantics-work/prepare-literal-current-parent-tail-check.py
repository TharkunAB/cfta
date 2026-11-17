from pathlib import Path
import hashlib
import json
import shlex
import tempfile

root = Path('/home/tritlo/Code/mcfta')
base = root / 'lean/restart-evidence'
runtime = base / '20261117-literal-current-parent-tail-check'
names = ['20261117-captured-current-resource-export-doc-scope-metadata-repair',
    '20261117-literal-current-parent-tail-goal-unfold-repair',
    '20261117-literal-tuple-current-original-budget-export-draft',
    '20261117-literal-tuple-current-held-cut-draft']
packets = [base / name for name in names]
sha = lambda data: hashlib.sha256(data).hexdigest()
for packet in packets:
    manifest = json.loads((packet / 'MANIFEST.json').read_text())
    for name, entry in manifest.get('files', manifest).items():
        assert sha((packet / name).read_bytes()) == (entry['sha256'] if isinstance(entry, dict) else entry), (packet, name)
owner = root / 'lean/MicroCFTA/SourcePruningEnumerationSharedEagerReservation.lean'
old = owner.read_bytes()
assert len(old) == 2050962 and sha(old) == 'dead99f476cf61b941470050bc938c1ad5bdd30a251b9ac6a1761d19e44bcaee'
prefix = b'import MicroCFTA.SourcePruningEnumerationStagedChildInvocation\n'
prefix += b'import MicroCFTA.SourcePruningEnumerationSharedInvocationInversions\n'
prefix += b'import MicroCFTA.SourcePruningEnumerationGuardedInvocationTransport\n\n'
append = b'\n'.join((packet / 'APPEND.lean.txt').read_bytes() for packet in packets)
assembled = prefix + old + b'\n' + append
assert assembled[len(prefix):len(prefix) + len(old)] == old
probes = b'\n'.join((packet / 'PROBES.lean.txt').read_bytes() for packet in packets)
assert probes.count(b'#print axioms ') == 10
old_probes = (base / '20261117-source-demand-causal-publication/ResourceProbes208.lean.txt').read_bytes()
assert old_probes.count(b'#print axioms ') == 208
runtime.mkdir()
source = runtime / 'source/MicroCFTA' / owner.name
source.parent.mkdir(parents=True)
source.write_bytes(assembled + b'\n' + old_probes + b'\n' + probes)
(runtime / 'OWNER-BEFORE.lean.txt').write_bytes(old)
(runtime / 'IMPORT-PREFIX.lean.txt').write_bytes(prefix)
(runtime / 'APPEND.lean.txt').write_bytes(append)
(runtime / 'NEW-PROBES.lean.txt').write_bytes(probes)
(runtime / 'PUBLIC-PROBES.lean.txt').write_bytes((packets[0] / 'PROBES.lean.txt').read_bytes())
(runtime / 'PRIVATE-PROBES.lean.txt').write_bytes(b'\n'.join((packet / 'PROBES.lean.txt').read_bytes() for packet in packets[1:]))
objects = Path(tempfile.mkdtemp(prefix='mcfta-literal-current-combined-'))
(runtime / 'objects.json').write_text(json.dumps({'path': str(objects)}, indent=2) + '\n')
selection = {'packets': names, 'owner': str(owner.relative_to(root)), 'old_owner_sha256': sha(old),
    'old_owner_bytes': len(old), 'old_owner_offset': len(prefix), 'import_prefix_sha256': sha(prefix),
    'append_sha256': sha(append), 'assembled_sha256': sha(assembled), 'reports': 218,
    'new_public_theorem_reports': 1, 'new_private_component_reports': 9,
    'old_owner_entire_exact_contiguous_block': True, 'all_new_proofs_maxHeartbeats': 200000}
(runtime / 'selection.json').write_text(json.dumps(selection, indent=2) + '\n')
imports = sorted({line.split()[1] for line in (prefix + old).decode().splitlines() if line.startswith('import ')})
command = 'exec lake env lean -j1 -DwarningAsError=true -R ' + shlex.quote(str(source.parent.parent))
command += ' -o ' + shlex.quote(str(objects / owner.with_suffix('.olean').name)) + ' ' + shlex.quote(str(source))
jobs = [('public-dependencies', 'exec lake build ' + ' '.join(imports), 0),
    ('owner-and-literal-current', command, 218)]
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
    'original_owner_resource_probes': 208, 'new_public_theorem_reports': 1,
    'new_private_component_reports': 9, 'actual_completed_tuple_current_internal_resources_proved': all(passed),
    'actual_completed_tuple_held_cut_proved': all(passed), 'full9374_all_history_proved': False,
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
print(json.dumps({'run': str(runtime), 'objects': str(objects), 'reports': 218,
    'old_owner_bytes_preserved': len(old), 'new_public_reports': 1, 'new_private_reports': 9,
    'assembled_sha256': sha(assembled)}))
