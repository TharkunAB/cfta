from pathlib import Path
import hashlib
import json
import shlex
import tempfile

root = Path('/home/tritlo/Code/mcfta')
base = root / 'lean/restart-evidence'
work = Path(__file__).parent
prior_run = base / '20261117-whole-branch-nested-held-publication'
prior_archive = base / '20261117-whole-branch-nested-held-checkpoint'
runtime = base / '20261117-application-class-birth-publication'
sha = lambda data: hashlib.sha256(data).hexdigest()
stage = json.loads((work / 'SOURCE-NORMAL-STAGING.json').read_text())
prior = json.loads((prior_run / 'checked.json').read_text())
assert len(prior['checks']) == 5 and all(c['exit'] == 0 and not c['nonstandard_axioms']
    and not c['diagnostics'] and not c['sorryAx'] for c in prior['checks'])
assert sha((root / stage['source_path']).read_bytes()) == stage['public_sha256']
baseline = json.loads((work / 'baseline-source-pins.json').read_text())
assert len(baseline) == 6241
assert {str(p.relative_to(root)) for p in (root / 'lean/MicroCFTA').glob('*.lean')} == set(baseline) | {stage['source_path']}
for name, digest in baseline.items():
    data = (work / 'AUDIT-BEFORE.lean.txt').read_bytes() if name == 'lean/MicroCFTA/Audit.lean' else (root / name).read_bytes()
    assert sha(data) == digest, name
runtime.mkdir()
objects = Path(tempfile.mkdtemp(prefix='mcfta-application-birth-publication-'))
(runtime / 'objects.json').write_text(json.dumps({'path': str(objects)}, indent=2) + '\n')
public = (work / 'PUBLIC-PROBES.lean.txt').read_bytes()
(runtime / 'PUBLIC-PROBES.lean.txt').write_bytes(public)
source = runtime / 'source/MicroCFTA/SourceSynthesisApplicationClassBirth.lean'
source.parent.mkdir(parents=True)
source.write_bytes((root / stage['source_path']).read_bytes() + b'\n' + public)
independent = runtime / 'IndependentProbes.lean'
independent.write_bytes(b'import MicroCFTA.SourceSynthesisApplicationClassBirth\n'
                        + (prior_run / 'IndependentProbes.lean').read_bytes() + b'\n' + public)
assert independent.read_bytes().count(b'#print axioms ') == 243
binding = {'prior_checkpoint': '2855a1f7b2664fc1677bf50a43a50d35f9442136',
    'prior_archive_manifest_sha256': sha((prior_archive / 'manifest.json').read_bytes()),
    'prior_checked_sha256': sha((prior_run / 'checked.json').read_bytes()),
    'prior_pins_sha256': sha((prior_run / 'source-pins.json').read_bytes()),
    'prior_source_files': 6241, 'inherited_reports': 365, 'fresh_reports': 1,
    'old_normal_sources_byte_exact_except_audit': 6240,
    'old_audit_bytes_retained_after_one_import': True,
    'old_toolchain_and_proof_inputs_reverified': True,
    'new_global_scope_or_model_claim': False}
(runtime / 'INHERITANCE-SELECTION.json').write_text(json.dumps(binding, indent=2) + '\n')
command = ['lake', 'env', 'lean', '-j1', '-DwarningAsError=true', '-R', str(source.parent.parent),
           '-o', str(objects / 'ApplicationClassBirth.olean'), str(source)]
strict = runtime / 'strict-new-and-bind.py'
strict.write_text('''from pathlib import Path
import gzip
import hashlib
import json
import subprocess

root = Path('/home/tritlo/Code/mcfta')
runtime = Path(__file__).parent
prior = root / 'lean/restart-evidence/20261117-whole-branch-nested-held-publication'
archive = root / 'lean/restart-evidence/20261117-whole-branch-nested-held-checkpoint'
work = root / 'lean/restart-evidence/20261117-application-class-birth-work'
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
print(json.dumps({'inherited_component_reports_verified': 365,
                  'fresh_component_reports_expected': 1,
                  'old_sources_and_toolchain_byte_exact': True}), flush=True)
'''+ 'subprocess.run(' + repr(command) + ', check=True)\n')
template = (base / stage['normal_check'] / 'check.py').read_text()
driver = template[:template.index('\njobs =')]
jobs = [('public-build', 'exec lake build', 0),
        ('strict-new-component-and-prior-bindings', 'exec python3 ' + shlex.quote(str(strict)), 1),
        ('independent-imports', 'exec lake env lean -j1 -DwarningAsError=true ' + shlex.quote(str(independent)), 243),
        ('audit-build', 'exec lake build MicroCFTA.Audit', 0),
        ('audit-strict', 'exec lake env lean -j1 -DwarningAsError=true MicroCFTA/Audit.lean', 648)]
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
report.update(source_files=6242, direct_audit_imports=5242, individual_reports=648,
    independent_reports=243, resource_and_component_probes=366,
    fresh_resource_component_reports=1, inherited_resource_component_reports=365,
    resource_component_evidence='one fresh strict report plus 365 prior reports with archive, source and toolchain bindings',
    new_component_reports=1, new_theorem_reports=1, new_modules=1, new_public_theorems=1,
    new_private_component_reports=0, new_public_component_reports=1,
    new_relation_declaration_checks=0, owner_resource_probes=250, previous_owner_resource_probes=250,
    old_non_audit_source_files_byte_exact=6240, entire_previous_resource_owner_byte_exact=True,
    old_owner_offset=0, old_owner_bytes_preserved_contiguously=(root / 'lean/MicroCFTA/SourcePruningEnumerationSharedEagerReservation.lean').stat().st_size,
    application_class_birth_proved=True, original_0976_header_exact=True,
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
files += [p for p in runtime.iterdir() if p.is_file()]
files += [source, Path(__file__), work / 'SOURCE-NORMAL-STAGING.json', work / 'baseline-source-pins.json', work / 'AUDIT-BEFORE.lean.txt']
(runtime / 'source-pins.json').write_text(json.dumps({str(p.relative_to(root)): sha(p.read_bytes()) for p in files}, indent=2) + '\n')
print(json.dumps({'run': str(runtime), 'gates': 5, 'fresh_component_reports': 1,
                  'inherited_component_reports': 365, 'independent_reports': 243, 'audit_reports': 648,
                  'objects': str(objects)}))
