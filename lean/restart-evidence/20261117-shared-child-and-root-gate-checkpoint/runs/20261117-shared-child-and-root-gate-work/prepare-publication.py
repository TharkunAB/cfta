from pathlib import Path
import hashlib
import json
import re
import shlex
import tempfile

root = Path('/home/tritlo/Code/mcfta')
base = root / 'lean/restart-evidence'
work = Path(__file__).parent
prior_run = base / '20261117-selected-row-and-prefix-publication'
prior_archive = base / '20261117-selected-row-and-prefix-checkpoint'
runtime = base / '20261117-shared-child-and-root-gate-publication'
sha = lambda data: hashlib.sha256(data).hexdigest()
stage = json.loads((work / 'SOURCES-NORMAL-STAGING.json').read_text())
components = stage['components']
prior = json.loads((prior_run / 'checked.json').read_text())
assert len(prior['checks']) == 5 and all(c['exit'] == 0 and not c['nonstandard_axioms']
    and not c['diagnostics'] and not c['sorryAx'] for c in prior['checks'])
baseline = json.loads((work / 'baseline-source-pins.json').read_text())
assert len(baseline) == 6244
assert {str(p.relative_to(root)) for p in (root / 'lean/MicroCFTA').glob('*.lean')} == set(baseline) | {c['source_path'] for c in components}
for name, digest in baseline.items():
    data = (work / 'AUDIT-BEFORE.lean.txt').read_bytes() if name == 'lean/MicroCFTA/Audit.lean' else (root / name).read_bytes()
    assert sha(data) == digest, name
runtime.mkdir()
objects = Path(tempfile.mkdtemp(prefix='mcfta-source-child-gate-publication-'))
(runtime / 'objects.json').write_text(json.dumps({'path': str(objects)}, indent=2) + '\n')
public = (work / 'PUBLIC-PROBES.lean.txt').read_bytes()
(runtime / 'PUBLIC-PROBES.lean.txt').write_bytes(public)
commands = []
strict_sources = []
fresh_count = 0
for component in components:
    normal = root / component['source_path']
    assert sha(normal.read_bytes()) == component['raw_sha256']
    helpers = re.findall(r'^private theorem ([A-Za-z0-9_]+)', normal.read_text(), re.M)
    probes = ''
    for name in helpers + [component['theorem']]:
        qname = 'MicroCFTA.' + component['module'] + '.' + name
        probes += '#check @' + qname + '\n#print axioms ' + qname + '\n'
    fresh_count += len(helpers) + 1
    source = runtime / 'source/MicroCFTA' / normal.name
    source.parent.mkdir(parents=True, exist_ok=True)
    source.write_bytes(normal.read_bytes() + b'\n' + probes.encode())
    (runtime / (component['module'] + '-PROBES.lean.txt')).write_text(probes)
    strict_sources.append(source)
    commands.append(['lake', 'env', 'lean', '-j1', '-DwarningAsError=true', '-R',
        str(source.parent.parent), '-o', str(objects / (component['module'] + '.olean')), str(source)])
assert fresh_count == 3
independent = runtime / 'IndependentProbes.lean'
imports = ''.join('import MicroCFTA.' + c['module'] + '\n' for c in components).encode()
independent.write_bytes(imports + (prior_run / 'IndependentProbes.lean').read_bytes() + b'\n' + public)
assert independent.read_bytes().count(b'#print axioms ') == 247
binding = {'prior_checkpoint': '3400a25f3f1d302f631af6c9561bcbcb20277d85',
    'prior_archive_manifest_sha256': sha((prior_archive / 'manifest.json').read_bytes()),
    'prior_checked_sha256': sha((prior_run / 'checked.json').read_bytes()),
    'prior_pins_sha256': sha((prior_run / 'source-pins.json').read_bytes()),
    'prior_source_files': 6244, 'inherited_reports': 374, 'fresh_reports': 3,
    'old_normal_sources_byte_exact_except_audit': 6243,
    'old_audit_bytes_retained_after_two_imports': True,
    'old_toolchain_and_proof_inputs_reverified': True}
(runtime / 'INHERITANCE-SELECTION.json').write_text(json.dumps(binding, indent=2) + '\n')
strict = runtime / 'strict-new-and-bind.py'
strict.write_text('''from pathlib import Path
import gzip
import hashlib
import json
import subprocess

root = Path('/home/tritlo/Code/mcfta')
runtime = Path(__file__).parent
prior = root / 'lean/restart-evidence/20261117-selected-row-and-prefix-publication'
archive = root / 'lean/restart-evidence/20261117-selected-row-and-prefix-checkpoint'
work = root / 'lean/restart-evidence/20261117-shared-child-and-root-gate-work'
sha = lambda data: hashlib.sha256(data).hexdigest()
selection = json.loads((runtime / 'INHERITANCE-SELECTION.json').read_text())
assert sha((archive / 'manifest.json').read_bytes()) == selection['prior_archive_manifest_sha256']
committed = subprocess.check_output(['git', 'show', selection['prior_checkpoint'] + ':'
    + str((archive / 'manifest.json').relative_to(root))], cwd=root)
assert committed == (archive / 'manifest.json').read_bytes()
subprocess.run(['python3', str(archive / 'verify.py')], check=True)
records = json.loads((archive / 'archived-inputs.json').read_text())
for name in ['checked.json', 'source-pins.json']:
    path = prior / name
    record = next(item for item in records if item['original'] == str(path))
    archived = (archive / record['archived']).read_bytes()
    if record['gzip']:
        archived = gzip.decompress(archived)
    assert archived == path.read_bytes()
assert sha((prior / 'checked.json').read_bytes()) == selection['prior_checked_sha256']
assert sha((prior / 'source-pins.json').read_bytes()) == selection['prior_pins_sha256']
for name, digest in json.loads((prior / 'source-pins.json').read_text()).items():
    data = (work / 'AUDIT-BEFORE.lean.txt').read_bytes() if name == 'lean/MicroCFTA/Audit.lean' else (root / name).read_bytes()
    assert sha(data) == digest, name
print(json.dumps({'inherited_component_reports_verified': 374,
                  'fresh_component_reports_expected': 3,
                  'old_sources_and_toolchain_byte_exact': True}), flush=True)
'''+ 'commands = ' + repr(commands) + '\nfor command in commands:\n    subprocess.run(command, check=True)\n')
template = (base / components[1]['check'] / 'check.py').read_text()
driver = template[:template.index('\njobs =')]
jobs = [('public-build', 'exec lake build', 0),
        ('strict-new-components-and-prior-bindings', 'exec python3 ' + shlex.quote(str(strict)), 3),
        ('independent-imports', 'exec lake env lean -j1 -DwarningAsError=true ' + shlex.quote(str(independent)), 247),
        ('audit-build', 'exec lake build MicroCFTA.Audit', 0),
        ('audit-strict', 'exec lake env lean -j1 -DwarningAsError=true MicroCFTA/Audit.lean', 652)]
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
for name in ['checks', 'limits', 'at', 'audited_theorems']:
    report.pop(name, None)
report.update(source_files=6246, direct_audit_imports=5246, individual_reports=652,
    independent_reports=247, resource_and_component_probes=377,
    fresh_resource_component_reports=3, inherited_resource_component_reports=374,
    resource_component_evidence='three fresh strict reports plus 374 prior reports with archive, source and toolchain bindings',
    new_component_reports=3, new_theorem_reports=3, new_modules=2, new_public_theorems=2,
    new_private_component_reports=1, new_public_component_reports=2,
    new_relation_declaration_checks=0, owner_resource_probes=250, previous_owner_resource_probes=250,
    old_non_audit_source_files_byte_exact=6243, entire_previous_resource_owner_byte_exact=True,
    actual_shared_program_child_fresh_mark_birth_proved=True,
    actual_original_raw_root_outer_empty_gate_false_proved=True,
    original_81e3_header_exact=True,
    first_34a_to_7e1c_header_whitespace_only=True,
    haskell_refolded_root_outer_gate_correspondence_proved=False,
    actual_six_fuel_selected_row_fields_proved=True,
    actual_six_fuel_prefix_program_slots_proved=True,
    original_8cf8_and_b17f_headers_exact=True,
    future_prefix_validity_supplier_required=False,
    whole_history_program_mark_production_proved=False,
    source_to_arbitrary_current_row_fields_proved=False,
    source_type_marker_class_consistency_proved=False, joint_finite_completion_proved=False,
    haskell_changed=False, proof_limits='unchanged defaults')
driver += 'report = ' + repr(report) + '\n'
driver += '''report.update(checks=checks, limits=limits, at=datetime.datetime.now().astimezone().isoformat(),
              audited_theorems=int(match.group(1)))
(runtime / 'checked.json').write_text(json.dumps(report, indent=2) + '\\n')
print(json.dumps(report), flush=True)
'''
(runtime / 'check.py').write_text(driver)
files = list((root / 'lean/MicroCFTA').glob('*.lean'))
files += [root / name for name in ['shell.nix', 'lean/lean-toolchain', 'lean/lakefile.toml', 'lean/lake-manifest.json']]
files += [p for p in runtime.iterdir() if p.is_file()] + strict_sources
files += [Path(__file__), work / 'SOURCES-NORMAL-STAGING.json', work / 'baseline-source-pins.json', work / 'AUDIT-BEFORE.lean.txt']
(runtime / 'source-pins.json').write_text(json.dumps({str(p.relative_to(root)): sha(p.read_bytes()) for p in files}, indent=2) + '\n')
print(json.dumps({'run': str(runtime), 'gates': 5, 'fresh_component_reports': 3,
                  'inherited_component_reports': 374, 'independent_reports': 247,
                  'audit_reports': 652, 'objects': str(objects)}))
