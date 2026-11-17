from pathlib import Path
import ast
import hashlib
import json
import tempfile

root = Path('/home/tritlo/Code/mcfta')
base = root / 'lean/restart-evidence'
work = Path(__file__).parent
previous = base / '20261117-source-demand-causal-publication'
runtime = base / '20261117-intermediate-semantics-publication'
sha = lambda data: hashlib.sha256(data).hexdigest()
prior = json.loads((previous / 'checked.json').read_text())
specs = json.loads((work / 'publication-selection.json').read_text())
kinds = json.loads((work / 'publication-report-kinds.json').read_text())
assert specs and set(kinds) == {row[0] for row in specs}
assert {row[0] for row in specs} >= {
    'SourcePruningEnumerationTopArrowInput', 'SourceSynthesisCurrentUniverseTerminalMarkerDemand',
    'SourceSynthesisCurrentUniverseUnfoldedRowPreparation', 'SourcePruningEnumerationGuardedInvocationTransport'}
owner_receipt = json.loads((work / 'OWNER-EXPORT-NORMAL-STAGING.json').read_text())
owner_name = 'lean/MicroCFTA/SourcePruningEnumerationSharedEagerReservation.lean'
owner = root / owner_name
owner_before = (base / owner_receipt['normal_check'] / 'OWNER-BEFORE.lean.txt').read_bytes()
owner_after = owner.read_bytes()
assert sha(owner_before) == owner_receipt['old_owner_sha256']
assert sha(owner_after) == owner_receipt['assembled_sha256']
assert owner_after[owner_receipt.get('old_owner_offset', 0):
    owner_receipt.get('old_owner_offset', 0) + len(owner_before)] == owner_before


def verify_pin(name, digest):
    actual = (root / name).read_bytes()
    if name == owner_name and digest == sha(owner_before):
        assert actual == owner_after
    else:
        assert sha(actual) == digest, name


for name, folder, digest, check_name in specs:
    result = json.loads((base / check_name / 'checked.json').read_text())
    assert all(result['passed'])
    for path, pin in json.loads((base / check_name / 'source-pins.json').read_text()).items():
        verify_pin(path, pin)
    assert sha((base / folder / (name + '.lean')).read_bytes()) == digest
owner_result = json.loads((base / owner_receipt['normal_check'] / 'checked.json').read_text())
assert all(owner_result['passed'])
for path, pin in json.loads((base / owner_receipt['normal_check'] / 'source-pins.json').read_text()).items():
    verify_pin(path, pin)
old_sources = {name: digest for name, digest in json.loads((previous / 'source-pins.json').read_text()).items()
               if name.startswith('lean/MicroCFTA/')}
assert len(old_sources) == prior['source_files'] == 6230
for name, digest in old_sources.items():
    verify_pin(name, digest)
runtime.mkdir()
audit = root / 'lean/MicroCFTA/Audit.lean'
(runtime / 'AUDIT-BEFORE.lean.txt').write_bytes(audit.read_bytes())
(runtime / 'OWNER-BEFORE.lean.txt').write_bytes(owner_before)
(runtime / 'OWNER-WITH-EXPORTS.lean.txt').write_bytes(owner_after)
public_probes = b''
transformations = []
for name, folder, digest, check_name in specs:
    raw = (base / folder / (name + '.lean')).read_bytes()
    assert sha(raw) == digest and b'set_option maxHeartbeats' not in raw
    source = root / 'lean/MicroCFTA' / (name + '.lean')
    assert source.read_bytes() == raw
    public_probes += b'\n' + (base / folder / 'PROBES.lean.txt').read_bytes()
    transformations.append({'module': name, 'packet': folder, 'checked_raw_sha256': digest,
        'public_sha256': digest, 'statements_definitions_and_proofs_unchanged': True})
owner_packet = base / owner_receipt['packet']
owner_check = base / owner_receipt['normal_check']
owner_probes = (owner_check / 'PUBLIC-PROBES.lean.txt').read_bytes() if (owner_check / 'PUBLIC-PROBES.lean.txt').exists() else (owner_packet / 'PROBES.lean.txt').read_bytes()
private_probes = (owner_check / 'PRIVATE-PROBES.lean.txt').read_bytes() if (owner_check / 'PRIVATE-PROBES.lean.txt').exists() else b''
private_reports = private_probes.count(b'#print axioms ')
assert private_reports == owner_receipt.get('private_reports', 0)
public_probes += b'\n' + owner_probes
new_reports = public_probes.count(b'#print axioms ')
theorem_reports = sum(item['theorems'] for item in kinds.values()) + owner_receipt['reports']
declaration_reports = sum(item['declarations'] for item in kinds.values())
assert new_reports == theorem_reports + declaration_reports
declaration_checks = sum(item.get('declaration_checks', 0) for item in kinds.values())
declaration_checks += owner_receipt.get('declaration_checks', 0)
imports = b''.join(('import MicroCFTA.' + row[0] + '\n').encode() for row in specs)
old_audit = audit.read_bytes()
audit.write_bytes(imports + old_audit + b'\n' + public_probes)
assert audit.read_bytes().split(b'\n', len(specs))[len(specs)].startswith(old_audit)
source_count = prior['source_files'] + len(specs)
audit_count = prior['direct_audit_imports'] + len(specs)
audit_reports = prior['individual_reports'] + new_reports
resource_reports = prior['resource_and_component_probes'] + new_reports + private_reports
independent_reports = prior['independent_reports'] + new_reports
assert len(list((root / 'lean/MicroCFTA').glob('*.lean'))) == source_count
assert sum(line.startswith('import ') for line in audit.read_text().splitlines()) == audit_count
assert audit.read_bytes().count(b'#print axioms ') == audit_reports
objects = Path(tempfile.mkdtemp(prefix='mcfta-intermediate-semantics-publication-'))
(runtime / 'objects.json').write_text(json.dumps({'path': str(objects)}, indent=2) + '\n')
(runtime / 'selection.json').write_text(json.dumps(specs, indent=2) + '\n')
(runtime / 'source-transformations.json').write_text(json.dumps(transformations, indent=2) + '\n')
(runtime / 'owner-export.json').write_text(json.dumps(owner_receipt, indent=2) + '\n')
probe_imports = b'import MicroCFTA.SourcePruningEnumerationSharedEagerReservation\n' + imports
(runtime / 'NewComponentProbes.lean').write_bytes(probe_imports + public_probes)
(runtime / 'ResourceProbes208.lean.txt').write_bytes((previous / 'ResourceProbes208.lean.txt').read_bytes())
(runtime / 'PrivateCurrentProbes.lean.txt').write_bytes(private_probes)
source = runtime / 'source/MicroCFTA' / owner.name
source.parent.mkdir(parents=True)
source.write_bytes(owner_after + b'\n' + (runtime / 'ResourceProbes208.lean.txt').read_bytes() + b'\n' + private_probes)
tree = ast.parse((previous / 'strict-modules.py').read_text())
commands = ast.literal_eval(next(node.value for node in tree.body if isinstance(node, ast.Assign)))
for index, command in enumerate(commands):
    command[command.index('-o') + 1] = str(objects / (str(index).zfill(3) + '-' + Path(command[-1]).stem + '.olean'))
    if index == 0:
        command[command.index('-R') + 1] = str(source.parent.parent)
        command[-1] = str(source)
for name, _, _, _ in specs:
    commands.append(['lake', 'env', 'lean', '-j1', '-DwarningAsError=true', '-o',
        str(objects / (name + '.olean')), str(root / 'lean/MicroCFTA' / (name + '.lean'))])
commands.append(['lake', 'env', 'lean', '-j1', '-DwarningAsError=true', '-o',
    str(objects / 'CurrentNewComponentProbes.olean'), str(runtime / 'NewComponentProbes.lean')])
strict = runtime / 'strict-modules.py'
strict.write_text('import subprocess\ncommands = ' + repr(commands) + '\nfor command in commands:\n    subprocess.run(command, check=True)\n')
independent = runtime / 'IndependentProbes.lean'
independent.write_bytes(probe_imports + (previous / 'IndependentProbes.lean').read_bytes() + b'\n' + public_probes)
assert independent.read_bytes().count(b'#print axioms ') == independent_reports
template = (base / specs[-1][3] / 'check.py').read_text()
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
report.update(source_files=source_count, direct_audit_imports=audit_count,
    individual_reports=audit_reports, independent_reports=independent_reports,
    resource_and_component_probes=resource_reports, new_component_reports=new_reports,
    new_theorem_reports=theorem_reports + private_reports, new_relation_declaration_reports=declaration_reports,
    new_modules=len(specs), new_public_theorems=theorem_reports,
    new_private_component_reports=private_reports, new_public_component_reports=new_reports,
    owner_resource_probes=208 + private_reports, previous_owner_resource_probes=208,
    new_relation_declaration_checks=declaration_checks,
    old_non_audit_non_owner_source_files_byte_exact=6228,
    old_owner_bytes_preserved_contiguously=len(owner_before), old_owner_proof_bodies_unchanged=True,
    old_owner_proof_limits_unchanged=True, new_owner_export_maxHeartbeats=200000,
    same_actual_tuple_selected_finalized_callback_packets_proved=True,
    source_terminal_marker_role_restriction_proved=True,
    original_source_unfolded_row_top_and_actual_arrow_input_proved=True,
    lower_original_inputs_same_guarded_eager_trace_proved=True,
    literal_callback_current_cut_proved=owner_result.get('actual_completed_tuple_current_internal_resources_proved', False),
    literal_callback_held_cut_proved=owner_result.get('actual_completed_tuple_held_cut_proved', False),
    actual_completed_tuple_current_produced=owner_result.get('actual_completed_tuple_current_internal_resources_proved', False),
    all_history_held_protection_proved=False, joint_finite_completion_proved=False,
    haskell_changed=False, source_pins_unchanged=True)
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
files += [source, Path(__file__), work / 'publication-selection.json', work / 'publication-report-kinds.json',
    work / 'OWNER-EXPORT-NORMAL-STAGING.json']
files += [Path(command[-1]) for command in commands]
(runtime / 'source-pins.json').write_text(json.dumps({str(path.relative_to(root)): sha(path.read_bytes())
    for path in files}, indent=2) + '\n')
print(json.dumps({'run': str(runtime), 'objects': str(objects), 'gates': 5,
    'source_files': source_count, 'resource_and_component_probes': resource_reports,
    'independent_reports': independent_reports, 'audit_reports': audit_reports}))
