from pathlib import Path
import ast
import hashlib
import json
import tempfile

root = Path('/home/tritlo/Code/mcfta')
base = root / 'lean/restart-evidence'
work = Path(__file__).parent
previous = base / '20261117-joint-held-ledger-publication'
runtime = base / '20261117-nested-held-entry-publication'
sha = lambda data: hashlib.sha256(data).hexdigest()
prior = json.loads((previous / 'checked.json').read_text())
guard = json.loads((work / 'GUARDED-NORMAL-STAGING.json').read_text())
owner = json.loads((work / 'OWNER-NORMAL-STAGING.json').read_text())
assert owner['all_owner_components_verified']
assert owner['closed_c316_original_budget_proved']
owner_path = root / owner['source_path']
normal_owner = owner_path.read_bytes()
assert sha(normal_owner) == owner['public_sha256']
assert sha((root / guard['source_path']).read_bytes()) == guard['public_sha256']
check = base / owner['normal_check']
assert all(json.loads((check / 'checked.json').read_text())['passed'])
for name, digest in json.loads((check / 'source-pins.json').read_text()).items():
    if name == owner['source_path']:
        assert digest == owner['old_owner_sha256']
    else:
        assert sha((root / name).read_bytes()) == digest, name
baseline = json.loads((work / 'baseline-source-pins.json').read_text())
assert len(baseline) == 6238
for name, digest in baseline.items():
    if name != owner['source_path']:
        assert sha((root / name).read_bytes()) == digest, name
offset = owner['old_owner_offset']
assert sha(normal_owner[offset:offset + owner['old_owner_bytes']]) == owner['old_owner_sha256']
assert len(list((root / 'lean/MicroCFTA').glob('*.lean'))) == 6239
runtime.mkdir()
audit = root / 'lean/MicroCFTA/Audit.lean'
old_audit = audit.read_bytes()
(runtime / 'AUDIT-BEFORE.lean.txt').write_bytes(old_audit)
imports = ('import MicroCFTA.' + guard['module'] + '\n').encode()
public = b'''#check MicroCFTA.SourcePruningEnumerationInvocationEventLedger.children_eager_ledger_to_guarded
#print axioms MicroCFTA.SourcePruningEnumerationInvocationEventLedger.children_eager_ledger_to_guarded
'''
if owner['public_capture_export_verified']:
    public += b'''#check MicroCFTA.SourcePruningEnumerationSharedEagerReservation.real_captured_invocation_nested_entries_held_at_original_budget
#print axioms MicroCFTA.SourcePruningEnumerationSharedEagerReservation.real_captured_invocation_nested_entries_held_at_original_budget
'''
new_public_reports = 1 + owner['new_public_theorems']
audit_reports = prior['individual_reports'] + new_public_reports
independent_reports = prior['independent_reports'] + new_public_reports
resource_reports = prior['resource_and_component_probes'] - 226 + owner['owner_reports'] + 3
assert public.count(b'#print axioms ') == new_public_reports
audit.write_bytes(imports + old_audit + b'\n' + public)
assert sum(line.startswith('import ') for line in audit.read_text().splitlines()) == 5239
assert audit.read_bytes().count(b'#print axioms ') == audit_reports
objects = Path(tempfile.mkdtemp(prefix='mcfta-nested-held-entry-publication-'))
(runtime / 'objects.json').write_text(json.dumps({'path': str(objects)}, indent=2) + '\n')
(runtime / 'selection.json').write_text(json.dumps({'guard': guard, 'owner': owner}, indent=2) + '\n')
(runtime / 'PUBLIC-PROBES.lean.txt').write_bytes(public)
owner_probes = (work / 'PreviousOwnerProbes226.lean.txt').read_bytes()
for name in owner['packets']:
    owner_probes += b'\n' + (base / name / 'PROBES.lean.txt').read_bytes()
assert owner_probes.count(b'#print axioms ') == owner['owner_reports']
owner_source = runtime / 'source/MicroCFTA/SourcePruningEnumerationSharedEagerReservation.lean'
owner_source.parent.mkdir(parents=True)
owner_source.write_bytes(normal_owner + b'\n' + owner_probes)
(runtime / 'OwnerComponentProbes.lean.txt').write_bytes(owner_probes)
guard_probes = (base / guard['packet'] / 'PROBES.lean.txt').read_bytes()
assert guard_probes.count(b'#print axioms ') == 3
guard_source = owner_source.parent / (guard['module'] + '.lean')
guard_source.write_bytes((root / guard['source_path']).read_bytes() + b'\n' + guard_probes)
(runtime / 'GuardedComponentProbes.lean.txt').write_bytes(guard_probes)
tree = ast.parse((previous / 'strict-modules.py').read_text())
commands = ast.literal_eval(next(node.value for node in tree.body if isinstance(node, ast.Assign)))
replaced = 0
for index, command in enumerate(commands):
    command[command.index('-o') + 1] = str(objects / (str(index).zfill(3) + '-' + Path(command[-1]).stem + '.olean'))
    if Path(command[-1]).name == 'SourcePruningEnumerationSharedEagerReservation.lean':
        command[command.index('-R') + 1] = str(owner_source.parent.parent)
        command[-1] = str(owner_source)
        replaced += 1
assert replaced == 1
commands.append(['lake', 'env', 'lean', '-j1', '-DwarningAsError=true', '-R',
                 str(guard_source.parent.parent), '-o', str(objects / 'GuardedEventLedgerComponents.olean'),
                 str(guard_source)])
strict = runtime / 'strict-modules.py'
strict.write_text('import subprocess\ncommands = ' + repr(commands) + '\nfor command in commands:\n    subprocess.run(command, check=True)\n')
independent = runtime / 'IndependentProbes.lean'
independent.write_bytes(imports + (previous / 'IndependentProbes.lean').read_bytes() + b'\n' + public)
assert independent.read_bytes().count(b'#print axioms ') == independent_reports
template = (check / 'check.py').read_text()
driver = template[:template.index('\njobs =')]
jobs = [('public-build', 'exec lake build', 0),
        ('strict-resource-and-component-modules', 'exec python3 ' + str(strict), resource_reports),
        ('independent-imports', 'exec lake env lean -j1 -DwarningAsError=true ' + str(independent), independent_reports),
        ('audit-build', 'exec lake build MicroCFTA.Audit', 0),
        ('audit-strict', 'exec lake env lean -j1 -DwarningAsError=true MicroCFTA/Audit.lean', audit_reports)]
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
report.update(source_files=6239, direct_audit_imports=5239, individual_reports=audit_reports,
    independent_reports=independent_reports, resource_and_component_probes=resource_reports,
    new_component_reports=owner['owner_reports'] - 226 + 3,
    new_theorem_reports=owner['owner_reports'] - 226 + 3, new_modules=1,
    new_public_theorems=new_public_reports,
    new_private_component_reports=owner['new_private_components'] + 2,
    new_public_component_reports=new_public_reports,
    new_relation_declaration_reports=0, new_relation_declaration_checks=5,
    owner_resource_probes=owner['owner_reports'], previous_owner_resource_probes=226,
    old_non_audit_source_files_byte_exact=6236, old_non_audit_non_owner_source_files_byte_exact=6236,
    entire_previous_resource_owner_byte_exact=False,
    old_owner_bytes_preserved_contiguously=owner['old_owner_bytes'], old_owner_offset=offset,
    old_owner_proof_bodies_unchanged=True, all_old_proof_limits_unchanged=True,
    source_pins_unchanged=True, guarded_same_event_ledger_transport_proved=True,
    literal_task_entry_held_factor_proved=True, closed_c316_original_budget_proved=True,
    literal_completed_invocation_nested_input_protection_proved=True,
    actual_captured_invocation_nested_input_protection_proved=owner['public_capture_export_verified'],
    whole_worker_joint_nested_protection_proved=False, nested_cut_protection_proved=False,
    original_c316_theorem_declaration_byte_exact=True, c316_historical_open_comment_removed=True,
    same_original_runtime_fuels=True, proof_limits='unchanged defaults',
    joint_finite_completion_proved=False, haskell_changed=False)
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
files += [owner_source, guard_source, Path(__file__), work / 'OWNER-NORMAL-STAGING.json',
          work / 'GUARDED-NORMAL-STAGING.json', work / 'baseline-source-pins.json']
(runtime / 'source-pins.json').write_text(json.dumps({str(p.relative_to(root)): sha(p.read_bytes())
                                                   for p in files}, indent=2) + '\n')
print(json.dumps({'run': str(runtime), 'objects': str(objects), 'gates': 5, 'source_files': 6239,
                  'resource_reports': resource_reports, 'independent_reports': independent_reports,
                  'audit_reports': audit_reports}))
