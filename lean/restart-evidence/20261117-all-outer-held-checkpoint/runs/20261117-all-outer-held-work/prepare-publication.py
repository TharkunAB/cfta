from pathlib import Path
import ast
import hashlib
import json
import tempfile

root = Path('/home/tritlo/Code/mcfta')
base = root / 'lean/restart-evidence'
work = Path(__file__).parent
previous = base / '20261117-intermediate-semantics-publication'
runtime = base / '20261117-all-outer-held-publication'
sha = lambda data: hashlib.sha256(data).hexdigest()
prior = json.loads((previous / 'checked.json').read_text())
receipt = json.loads((work / 'OWNER-NORMAL-STAGING.json').read_text())
leaf = json.loads((work / 'LEAF-NORMAL-STAGING.json').read_text())
assert receipt['all_history9374_proved'] and receipt['public9374_theorem_declaration_byte_exact']
check = base / receipt['normal_check']
result = json.loads((check / 'checked.json').read_text())
assert all(result['passed']) and result['all_history9374_proved']
owner_name = 'lean/MicroCFTA/SourcePruningEnumerationSharedEagerReservation.lean'
owner = root / owner_name
before = (check / 'OWNER-BEFORE.lean.txt').read_bytes()
after = owner.read_bytes()
assert sha(before) == receipt['old_owner_sha256']
assert sha(after) == receipt['assembled_sha256']
offset = receipt['old_owner_offset']
assert after[offset:offset + len(before)] == before
checked_after = (check / 'IMPORT-PREFIX.lean.txt').read_bytes() + before + b'\n' + (check / 'APPEND.lean.txt').read_bytes()
assert sha(checked_after) == receipt['checked_assembled_sha256']
assert after == checked_after.replace(b'-- OPEN target. No proof, axiom or theorem declaration is installed.\n', b'', 1)


def verify_pin(name, digest):
    current = (root / name).read_bytes()
    if name == owner_name and digest == sha(before):
        assert current == after
    else:
        assert sha(current) == digest, name


for name, digest in json.loads((check / 'source-pins.json').read_text()).items():
    verify_pin(name, digest)
leaf_check = base / leaf['normal_check']
assert all(json.loads((leaf_check / 'checked.json').read_text())['passed'])
for name, digest in json.loads((leaf_check / 'source-pins.json').read_text()).items():
    verify_pin(name, digest)
leaf_source = root / leaf['source_path']
assert sha(leaf_source.read_bytes()) == leaf['public_sha256'] == leaf['sha256']
old_sources = {name: digest for name, digest in json.loads((previous / 'source-pins.json').read_text()).items()
               if name.startswith('lean/MicroCFTA/')}
assert len(old_sources) == prior['source_files'] == 6235
for name, digest in old_sources.items():
    verify_pin(name, digest)
runtime.mkdir()
audit = root / 'lean/MicroCFTA/Audit.lean'
old_audit = audit.read_bytes()
public = (work / 'PUBLIC-PROBES.lean.txt').read_bytes()
public += b'\n' + (base / leaf['packet'] / 'PROBES.lean.txt').read_bytes()
private = (work / 'PRIVATE-PROBES.lean.txt').read_bytes()
assert public.count(b'#print axioms ') == 2 and private.count(b'#print axioms ') == 9
(runtime / 'AUDIT-BEFORE.lean.txt').write_bytes(old_audit)
(runtime / 'OWNER-BEFORE.lean.txt').write_bytes(before)
(runtime / 'OWNER-WITH-EXPORTS.lean.txt').write_bytes(after)
(runtime / 'PUBLIC-PROBES.lean.txt').write_bytes(public)
(runtime / 'PRIVATE-PROBES.lean.txt').write_bytes(private)
leaf_import = ('import MicroCFTA.' + leaf['module'] + '\n').encode()
audit.write_bytes(leaf_import + old_audit + b'\n' + public)
assert audit.read_bytes()[len(leaf_import):].startswith(old_audit)
assert len(list((root / 'lean/MicroCFTA').glob('*.lean'))) == 6236
assert sum(line.startswith('import ') for line in audit.read_text().splitlines()) == prior['direct_audit_imports'] + 1
audit_reports = prior['individual_reports'] + 2
resource_reports = prior['resource_and_component_probes'] + 11
independent_reports = prior['independent_reports'] + 2
assert audit.read_bytes().count(b'#print axioms ') == audit_reports
objects = Path(tempfile.mkdtemp(prefix='mcfta-all-outer-held-publication-'))
(runtime / 'objects.json').write_text(json.dumps({'path': str(objects)}, indent=2) + '\n')
(runtime / 'owner-staging.json').write_text(json.dumps(receipt, indent=2) + '\n')
import_owner = b'import MicroCFTA.SourcePruningEnumerationSharedEagerReservation\n' + leaf_import
(runtime / 'NewComponentProbes.lean').write_bytes(import_owner + public)
original_probes = (previous / 'ResourceProbes208.lean.txt').read_bytes()
previous_private = (previous / 'PrivateCurrentProbes.lean.txt').read_bytes()
assert original_probes.count(b'#print axioms ') == 208
assert previous_private.count(b'#print axioms ') == 9
(runtime / 'ResourceProbes208.lean.txt').write_bytes(original_probes)
(runtime / 'PrivatePreviousProbes.lean.txt').write_bytes(previous_private)
source = runtime / 'source/MicroCFTA' / owner.name
source.parent.mkdir(parents=True)
source.write_bytes(after + b'\n' + original_probes + b'\n' + previous_private + b'\n' + private)
tree = ast.parse((previous / 'strict-modules.py').read_text())
commands = ast.literal_eval(next(node.value for node in tree.body if isinstance(node, ast.Assign)))
for index, command in enumerate(commands):
    command[command.index('-o') + 1] = str(objects / (str(index).zfill(3) + '-' + Path(command[-1]).stem + '.olean'))
    if index == 0:
        command[command.index('-R') + 1] = str(source.parent.parent)
        command[-1] = str(source)
commands.append(['lake', 'env', 'lean', '-j1', '-DwarningAsError=true', '-o',
                 str(objects / (leaf['module'] + '.olean')), str(leaf_source)])
commands.append(['lake', 'env', 'lean', '-j1', '-DwarningAsError=true', '-o',
                 str(objects / 'OuterHeldPublicProbes.olean'), str(runtime / 'NewComponentProbes.lean')])
strict = runtime / 'strict-modules.py'
strict.write_text('import subprocess\ncommands = ' + repr(commands) + '\nfor command in commands:\n    subprocess.run(command, check=True)\n')
independent = runtime / 'IndependentProbes.lean'
independent.write_bytes(import_owner + (previous / 'IndependentProbes.lean').read_bytes() + b'\n' + public)
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
report.update(source_files=6236, direct_audit_imports=prior['direct_audit_imports'] + 1,
    individual_reports=audit_reports, independent_reports=independent_reports,
    resource_and_component_probes=resource_reports, new_component_reports=2, new_theorem_reports=11,
    new_relation_declaration_reports=0, new_modules=1, new_public_theorems=2,
    new_private_component_reports=9, new_public_component_reports=2,
    owner_resource_probes=prior['owner_resource_probes'] + 9,
    previous_owner_resource_probes=prior['owner_resource_probes'], new_relation_declaration_checks=0,
    old_non_audit_non_owner_source_files_byte_exact=6233,
    old_owner_bytes_preserved_contiguously=len(before), old_owner_offset=offset,
    old_owner_proof_bodies_unchanged=True, old_owner_proof_limits_unchanged=True,
    all_history9374_proved=True, all_history_held_protection_proved=True,
    actual_parked_all_later_outer_entries_held_history_proved=True,
    original_source_arrow_staged_provenance_proved=True,
    public9374_header_byte_exact=False, public9374_theorem_declaration_byte_exact=True,
    historical_open_comment_removed=True, shared5e48_predicate_byte_exact=True,
    same_original_runtime_fuels=True, new_proof_maxHeartbeats=200000,
    joint_finite_completion_proved=False, haskell_changed=False, source_pins_unchanged=True)
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
files += [source, Path(__file__), work / 'OWNER-NORMAL-STAGING.json', work / 'PUBLIC-PROBES.lean.txt',
          work / 'PRIVATE-PROBES.lean.txt', work / 'CHECK-TO-INSTALL.json', work / 'LEAF-NORMAL-STAGING.json']
files += [Path(command[-1]) for command in commands]
(runtime / 'source-pins.json').write_text(json.dumps({str(path.relative_to(root)): sha(path.read_bytes())
    for path in files}, indent=2) + '\n')
print(json.dumps({'run': str(runtime), 'objects': str(objects), 'gates': 5,
                 'resource_and_component_probes': resource_reports,
                 'independent_reports': independent_reports, 'audit_reports': audit_reports}))
