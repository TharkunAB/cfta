from pathlib import Path
import ast
import hashlib
import json
import tempfile

root = Path('/home/tritlo/Code/mcfta')
base = root / 'lean/restart-evidence'
work = Path(__file__).parent
previous = base / '20261117-all-outer-held-publication'
runtime = base / '20261117-joint-held-ledger-publication'
sha = lambda data: hashlib.sha256(data).hexdigest()
prior = json.loads((previous / 'checked.json').read_text())
core = json.loads((work / 'CORE-NORMAL-STAGING.json').read_text())
worker = json.loads((work / 'WORKER-NORMAL-STAGING.json').read_text())
specs = [core, worker]
for spec in specs:
    check = base / spec['normal_check']
    result = json.loads((check / 'checked.json').read_text())
    assert all(result['passed'])
    for name, digest in json.loads((check / 'source-pins.json').read_text()).items():
        assert sha((root / name).read_bytes()) == digest, name
    raw = (base / spec['packet'] / (spec['module'] + '.lean')).read_bytes()
    assert sha(raw) == spec['sha256']
    normal = (root / spec['source_path']).read_bytes()
    assert sha(normal) == spec['public_sha256']
    if spec is core:
        assert normal == raw
    else:
        assert normal == raw.replace(b'-- OPEN prospective target. No proof or declaration is installed.\n', b'', 1)
    assert b'set_option maxHeartbeats' not in normal
old_sources = {name: digest for name, digest in json.loads((previous / 'source-pins.json').read_text()).items()
               if name.startswith('lean/MicroCFTA/')}
assert len(old_sources) == prior['source_files'] == 6236
for name, digest in old_sources.items():
    assert sha((root / name).read_bytes()) == digest, name
runtime.mkdir()
audit = root / 'lean/MicroCFTA/Audit.lean'
old_audit = audit.read_bytes()
(runtime / 'AUDIT-BEFORE.lean.txt').write_bytes(old_audit)
public = b'''#check @MicroCFTA.SourcePruningEnumerationHeldJointCausalEventLedger.OuterEntriesHeld
#check MicroCFTA.SourcePruningEnumerationHeldJointCausalEventLedger.held_output_history_joint_event_ledger
#print axioms MicroCFTA.SourcePruningEnumerationHeldJointCausalEventLedger.held_output_history_joint_event_ledger
#check MicroCFTA.SourcePruningEnumerationHeldJointCausalEventLedger.held_prepared_history_joint_event_ledger
#print axioms MicroCFTA.SourcePruningEnumerationHeldJointCausalEventLedger.held_prepared_history_joint_event_ledger
'''
worker_probes = (base / worker['packet'] / 'PROBES.lean.txt').read_bytes()
assert worker_probes.count(b'#print axioms ') == 1
public += b'\n' + worker_probes
assert public.count(b'#print axioms ') == 3
imports = b''.join(('import MicroCFTA.' + spec['module'] + '\n').encode() for spec in specs)
audit.write_bytes(imports + old_audit + b'\n' + public)
assert audit.read_bytes()[len(imports):].startswith(old_audit)
assert len(list((root / 'lean/MicroCFTA').glob('*.lean'))) == 6238
assert sum(line.startswith('import ') for line in audit.read_text().splitlines()) == 5238
assert audit.read_bytes().count(b'#print axioms ') == 642
objects = Path(tempfile.mkdtemp(prefix='mcfta-joint-held-ledger-publication-'))
(runtime / 'objects.json').write_text(json.dumps({'path': str(objects)}, indent=2) + '\n')
(runtime / 'selection.json').write_text(json.dumps(specs, indent=2) + '\n')
(runtime / 'PUBLIC-PROBES.lean.txt').write_bytes(public)
(runtime / 'NewComponentProbes.lean').write_bytes(imports + worker_probes)
core_probes = (base / core['packet'] / 'PROBES.lean.txt').read_bytes()
assert core_probes.count(b'#print axioms ') == 11
(runtime / 'CoreComponentProbes.lean.txt').write_bytes(core_probes)
source = runtime / 'source/MicroCFTA' / (core['module'] + '.lean')
source.parent.mkdir(parents=True)
source.write_bytes((root / core['source_path']).read_bytes() + b'\n' + core_probes)
(runtime / 'ResourceProbes208.lean.txt').write_bytes((previous / 'ResourceProbes208.lean.txt').read_bytes())
tree = ast.parse((previous / 'strict-modules.py').read_text())
commands = ast.literal_eval(next(node.value for node in tree.body if isinstance(node, ast.Assign)))
for index, command in enumerate(commands):
    command[command.index('-o') + 1] = str(objects / (str(index).zfill(3) + '-' + Path(command[-1]).stem + '.olean'))
commands.append(['lake', 'env', 'lean', '-j1', '-DwarningAsError=true', '-R', str(source.parent.parent),
                 '-o', str(objects / 'HeldJointCoreComponents.olean'), str(source)])
for spec in specs:
    commands.append(['lake', 'env', 'lean', '-j1', '-DwarningAsError=true', '-o',
                     str(objects / (spec['module'] + '.olean')), str(root / spec['source_path'])])
commands.append(['lake', 'env', 'lean', '-j1', '-DwarningAsError=true', '-o',
                 str(objects / 'HeldJointWorkerPublic.olean'), str(runtime / 'NewComponentProbes.lean')])
strict = runtime / 'strict-modules.py'
strict.write_text('import subprocess\ncommands = ' + repr(commands) + '\nfor command in commands:\n    subprocess.run(command, check=True)\n')
independent = runtime / 'IndependentProbes.lean'
independent.write_bytes(imports + (previous / 'IndependentProbes.lean').read_bytes() + b'\n' + public)
assert independent.read_bytes().count(b'#print axioms ') == 237
template = (base / worker['normal_check'] / 'check.py').read_text()
driver = template[:template.index('\njobs =')]
jobs = [('public-build', 'exec lake build', 0),
        ('strict-resource-and-component-modules', 'exec python3 ' + str(strict), 336),
        ('independent-imports', 'exec lake env lean -j1 -DwarningAsError=true ' + str(independent), 237),
        ('audit-build', 'exec lake build MicroCFTA.Audit', 0),
        ('audit-strict', 'exec lake env lean -j1 -DwarningAsError=true MicroCFTA/Audit.lean', 642)]
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
report.update(source_files=6238, direct_audit_imports=5238, individual_reports=642,
    independent_reports=237, resource_and_component_probes=336, new_component_reports=3,
    new_theorem_reports=12, new_relation_declaration_reports=0, new_modules=2,
    new_public_theorems=3, new_private_component_reports=9, new_public_component_reports=3,
    new_relation_declaration_checks=1, owner_resource_probes=226, previous_owner_resource_probes=226,
    old_non_audit_source_files_byte_exact=6235, old_non_audit_non_owner_source_files_byte_exact=6234,
    entire_previous_resource_owner_byte_exact=True, old_owner_bytes_preserved_contiguously=2222363,
    old_owner_offset=0, all_old_proof_limits_unchanged=True,
    core_shared_predicate_and_headers_byte_exact=True, worker_a3c_theorem_declaration_byte_exact=True,
    worker_historical_open_comment_removed=True, joint_held_event_history_proved=True,
    actual_parked_same_joint_ledger_outer_entries_held_history_proved=True,
    joint_recorded_outer_entry_protection_proved=True, nested_cut_protection_proved=False,
    actual_source_type_marker_role_preservation_proved=False, joint_finite_completion_proved=False,
    same_original_runtime_fuels=True, proof_limits='unchanged defaults', haskell_changed=False,
    source_pins_unchanged=True)
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
files += [path for path in runtime.iterdir() if path.is_file()]
files += [Path(command[-1]) for command in commands]
files += [source, Path(__file__), work / 'CORE-NORMAL-STAGING.json', work / 'WORKER-NORMAL-STAGING.json']
(runtime / 'source-pins.json').write_text(json.dumps({str(path.relative_to(root)): sha(path.read_bytes())
    for path in files}, indent=2) + '\n')
print(json.dumps({'run': str(runtime), 'objects': str(objects), 'gates': 5,
                 'source_files': 6238, 'resource_reports': 336, 'independent_reports': 237, 'audit_reports': 642}))
