from pathlib import Path
import ast
import hashlib
import json
import tempfile

root = Path('/home/tritlo/Code/mcfta')
base = root / 'lean/restart-evidence'
work = Path(__file__).parent
previous = base / '20261117-nested-held-entry-publication'
runtime = base / '20261117-whole-branch-nested-held-publication'
sha = lambda data: hashlib.sha256(data).hexdigest()
stage = json.loads((work / 'SOURCE-NORMAL-STAGING.json').read_text())
prior = json.loads((previous / 'checked.json').read_text())
owner = root / stage['owner_source_path']
marker = root / stage['marker_source_path']
assert sha(owner.read_bytes()) == stage['owner_public_sha256']
assert sha(marker.read_bytes()) == stage['marker_public_sha256']
baseline = json.loads((work / 'baseline-source-pins.json').read_text())
for name, digest in baseline.items():
    if name != stage['owner_source_path']:
        assert sha((root / name).read_bytes()) == digest, name
offset = stage['old_owner_offset']
assert sha(owner.read_bytes()[offset:offset + stage['old_owner_bytes']]) == stage['old_owner_sha256']
assert len(list((root / 'lean/MicroCFTA').glob('*.lean'))) == 6241
runtime.mkdir()
audit = root / 'lean/MicroCFTA/Audit.lean'
old_audit = audit.read_bytes()
(runtime / 'AUDIT-BEFORE.lean.txt').write_bytes(old_audit)
imports = b'import MicroCFTA.SourcePruningEnumerationWholeEventEntryProtection\n'
imports += ('import MicroCFTA.' + stage['marker_module'] + '\n').encode()
public = b'''#check MicroCFTA.SourcePruningEnumerationWholeEventEntryProtection.entries_held_append
#print axioms MicroCFTA.SourcePruningEnumerationWholeEventEntryProtection.entries_held_append
#check MicroCFTA.SourcePruningEnumerationParkedOuterHeldHistory.actual_parked_same_joint_ledger_all_entries_held_history
#print axioms MicroCFTA.SourcePruningEnumerationParkedOuterHeldHistory.actual_parked_same_joint_ledger_all_entries_held_history
#check MicroCFTA.SourceSynthesisCurrentUniverseTerminalMarkerNativeRestriction.original_universe_terminal_marker_native_restriction
#print axioms MicroCFTA.SourceSynthesisCurrentUniverseTerminalMarkerNativeRestriction.original_universe_terminal_marker_native_restriction
'''
audit.write_bytes(imports + old_audit + b'\n' + public)
assert sum(line.startswith('import ') for line in audit.read_text().splitlines()) == 5241
assert audit.read_bytes().count(b'#print axioms ') == 647
objects = Path(tempfile.mkdtemp(prefix='mcfta-whole-branch-publication-'))
(runtime / 'objects.json').write_text(json.dumps({'path': str(objects)}, indent=2) + '\n')
(runtime / 'PUBLIC-PROBES.lean.txt').write_bytes(public)
(runtime / 'selection.json').write_text(json.dumps(stage, indent=2) + '\n')
owner_probes = (work / 'PreviousOwnerProbes235.lean.txt').read_bytes()
for name in stage['owner_raw_packets']:
    owner_probes += b'\n' + (base / name / 'PROBES.lean.txt').read_bytes()
assert owner_probes.count(b'#print axioms ') == 250
source_dir = runtime / 'source/MicroCFTA'
source_dir.mkdir(parents=True)
owner_source = source_dir / owner.name
owner_source.write_bytes(owner.read_bytes() + b'\n' + owner_probes)
(runtime / 'OwnerComponentProbes.lean.txt').write_bytes(owner_probes)
tree = ast.parse((previous / 'strict-modules.py').read_text())
commands = ast.literal_eval(next(node.value for node in tree.body if isinstance(node, ast.Assign)))
replaced = 0
for index, command in enumerate(commands):
    command[command.index('-o') + 1] = str(objects / (str(index).zfill(3) + '-' + Path(command[-1]).stem + '.olean'))
    if Path(command[-1]).name == owner.name:
        command[command.index('-R') + 1] = str(source_dir.parent)
        command[-1] = str(owner_source)
        replaced += 1
assert replaced == 1
components = [
    ('SourcePruningEnumerationWholeEventEntryProtection', '20261117-whole-event-entry-protection-draft'),
    (stage['marker_module'], stage['marker_packet']),
]
for module, packet in components:
    normal = root / 'lean/MicroCFTA' / (module + '.lean')
    probes = (base / packet / 'PROBES.lean.txt').read_bytes()
    assert probes.count(b'#print axioms ') == 1
    source = source_dir / normal.name
    source.write_bytes(normal.read_bytes() + b'\n' + probes)
    commands.append(['lake', 'env', 'lean', '-j1', '-DwarningAsError=true', '-R', str(source_dir.parent),
                     '-o', str(objects / (module + '.olean')), str(source)])
strict = runtime / 'strict-modules.py'
strict.write_text('import subprocess\ncommands = ' + repr(commands) + '\nfor command in commands:\n    subprocess.run(command, check=True)\n')
independent = runtime / 'IndependentProbes.lean'
independent.write_bytes(imports + (previous / 'IndependentProbes.lean').read_bytes() + b'\n' + public)
assert independent.read_bytes().count(b'#print axioms ') == 242
template = (base / stage['marker_normal_check'] / 'check.py').read_text()
driver = template[:template.index('\njobs =')]
jobs = [
    ('public-build', 'exec lake build', 0),
    ('strict-resource-and-component-modules', 'exec python3 ' + str(strict), 365),
    ('independent-imports', 'exec lake env lean -j1 -DwarningAsError=true ' + str(independent), 242),
    ('audit-build', 'exec lake build MicroCFTA.Audit', 0),
    ('audit-strict', 'exec lake env lean -j1 -DwarningAsError=true MicroCFTA/Audit.lean', 647),
]
driver += '\njobs = ' + repr(jobs) + '''
for name, command, count in jobs:
    run(name, command, count)
assert len(checks) == 5
assert all(c['exit'] == 0 and not c['nonstandard_axioms'] and not c['diagnostics'] and not c['sorryAx']
           and (not job[2] or c['total_axiom_reports'] == job[2]) for c, job in zip(checks, jobs))
match = re.search(r'Checked axiom dependencies of (\\d+) MicroCFTA theorems\\.', (runtime / 'audit-strict.txt').read_text())
assert match
'''
report = dict(prior)
report.update(source_files=6241, direct_audit_imports=5241, individual_reports=647,
    independent_reports=242, resource_and_component_probes=365, owner_resource_probes=250,
    previous_owner_resource_probes=235, new_component_reports=17, new_theorem_reports=17,
    new_modules=2, new_public_theorems=3, new_private_component_reports=14,
    new_public_component_reports=3, new_relation_declaration_checks=1,
    old_non_audit_source_files_byte_exact=6237, old_non_audit_non_owner_source_files_byte_exact=6237,
    old_owner_bytes_preserved_contiguously=stage['old_owner_bytes'], old_owner_offset=offset,
    old_owner_proof_bodies_unchanged=True, all_old_proof_limits_unchanged=True,
    source_pins_unchanged=True, all_visible_operation_entries_held_proved=True,
    actual_parked_joint_ledger_all_visible_entries_held_history_proved=True,
    whole_worker_joint_nested_protection_proved=True,
    hidden_primitive_operation_inputs_recorded=False,
    source_terminal_marker_native_restriction_proved=True,
    source_terminal_marker_native_inhabitance_proved=False,
    actual_source_type_marker_role_preservation_proved=False,
    source_type_marker_class_consistency_proved=False,
    same_original_runtime_fuels=True, proof_limits='unchanged defaults',
    joint_finite_completion_proved=False, haskell_changed=False,
    component_owner_original_driver_completed=False,
    component_owner_explicit_recovery_receipt=True)
for name in ['checks', 'limits', 'at', 'audited_theorems']:
    report.pop(name, None)
driver += 'report = ' + repr(report) + '\n'
driver += '''report.update(checks=checks, limits=limits, at=datetime.datetime.now().astimezone().isoformat(),
              audited_theorems=int(match.group(1)))
(runtime / 'checked.json').write_text(json.dumps(report, indent=2) + '\\n')
print(json.dumps(report), flush=True)
'''
(runtime / 'check.py').write_text(driver)
files = list((root / 'lean/MicroCFTA').glob('*.lean'))
files += [root / name for name in ['shell.nix', 'lean/lean-toolchain', 'lean/lakefile.toml', 'lean/lake-manifest.json']]
files += [p for p in runtime.iterdir() if p.is_file()]
files += [Path(command[-1]) for command in commands]
files += [Path(__file__), work / 'SOURCE-NORMAL-STAGING.json', work / 'baseline-source-pins.json']
(runtime / 'source-pins.json').write_text(json.dumps({str(p.relative_to(root)): sha(p.read_bytes())
                                                   for p in files}, indent=2) + '\n')
print(json.dumps({'run': str(runtime), 'objects': str(objects), 'gates': 5, 'source_files': 6241,
                  'resource_reports': 365, 'independent_reports': 242, 'audit_reports': 647}))
