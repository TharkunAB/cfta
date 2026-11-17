from pathlib import Path
import ast
import hashlib
import json
import re
import tempfile

root = Path('/home/tritlo/Code/mcfta')
base = root / 'lean/restart-evidence'
control = base / '20261117-third-query-six-seed-publication-control-draft'
work = base / '20261117-third-query-node-seed-work'
assert Path(__file__).resolve().parent == work.resolve(), 'Root must review and copy this controller.'
assert Path(__file__).read_bytes() == (control / 'prepare-publication.py').read_bytes()
runtime = base / '20261117-third-query-six-seed-publication'
assert not runtime.exists(), 'Preserve earlier runs.'
prior_run = base / '20261117-warm-full-admission-identity-publication'
prior_archive = base / '20261117-warm-full-admission-identity-checkpoint'
prior_commit = 'c894b4e3fda56e1f8c275f02653f0bba3be7167a'
prior_manifest = '3def8e9ca8cd34af38b886efdb00295ac5599c9a53f71b3854a43763990e7160'
sha = lambda data: hashlib.sha256(data).hexdigest()
audit_name = 'lean/MicroCFTA/Audit.lean'
owner_name = 'lean/MicroCFTA/SourcePruningEnumerationSharedEagerReservation.lean'
owner_sha = '861927716556bffdeefb2ab403160e791b4ef62be50e11caab5209ca0cf73f93'
bound = set()


def verify(path, record):
    data = path.read_bytes()
    digest = record['sha256'] if isinstance(record, dict) else record
    assert sha(data) == digest, str(path)
    if isinstance(record, dict) and 'bytes' in record:
        assert len(data) == record['bytes'], str(path)
    bound.add(path)
    return data


def items(value):
    return list(value.items()) if isinstance(value, dict) else [(item['path'], item) for item in value]


def manifest_records(manifest):
    return [(item['path'], item) for item in manifest['artifacts']] if 'artifacts' in manifest else items(manifest['files'])


for name, record in json.loads((control / 'MANIFEST.json').read_text())['files'].items():
    verify(control / name, record)
bound.add(control / 'MANIFEST.json')
staging_control = base / '20261117-third-query-six-seed-staging-control-draft'
verify(staging_control / 'MANIFEST.json', 'f471e45e788bd4be7d6e7208ac8ffd364a1504a35245b249498c942539056f15')
for name, record in json.loads((staging_control / 'MANIFEST.json').read_text())['files'].items():
    verify(staging_control / name, record)
for name, record in json.loads((staging_control / 'SOURCE-PINS.json').read_text()).items():
    verify(root / name, record)
stage_path = work / 'SOURCES-NORMAL-STAGING.json'
stage = json.loads(stage_path.read_text())
assert stage == json.loads((control / 'EXPECTED-STAGE.json').read_text())
assert stage['prior_checkpoint'] == prior_commit
expected = stage['components']
overrides = {audit_name: str((work / 'Audit-BEFORE.lean.txt').relative_to(root))}
overrides.update({item['source_path']: item['old_snapshot'] for item in expected if item['kind'] == 'existing_owner_EOF'})
assert len(overrides) == 4 and stage['baseline_overrides'] == overrides
assert (stage['source_files'], stage['audit_imports'], stage['audit_reports'], stage['independent_reports']) == (6270, 5270, 709, 304)
assert (stage['new_modules'], stage['new_public_theorems'], stage['new_private_helpers'], stage['new_theorem_declarations'], stage['new_prop_definitions']) == (3, 7, 6, 13, 0)
assert (stage['fresh_reports'], stage['inherited_reports'], stage['combined_reports']) == (7, 496, 503)
baseline_path = work / 'baseline-source-pins.json'
baseline = json.loads(baseline_path.read_text())
assert len(baseline) == 6267 and len(expected) == 6
new_names = {item['source_path'] for item in expected if item['kind'] == 'new_module'}
assert len(new_names) == 3 and not new_names.intersection(baseline)
current = sorted((root / 'lean/MicroCFTA').glob('*.lean'))
assert {str(path.relative_to(root)) for path in current} == set(baseline) | new_names


def prior_bytes(name):
    path = root / overrides.get(name, name)
    bound.add(path)
    return path.read_bytes()


def verify_prior_pins(path):
    bound.add(path)
    for name, record in items(json.loads(path.read_text())):
        data = prior_bytes(name)
        assert sha(data) == (record['sha256'] if isinstance(record, dict) else record), name
        if isinstance(record, dict) and 'bytes' in record:
            assert len(data) == record['bytes'], name


for name, digest in baseline.items():
    assert sha(prior_bytes(name)) == digest, name
assert len(set(baseline) - set(overrides)) == 6263
old_audit = prior_bytes(audit_name)
assert len(old_audit) == stage['old_audit_bytes'] == 430643
assert sha(old_audit) == stage['old_audit_sha256'] == '760bbc31e363594987a026403384eeb0ee425456c091b6ed0a8e265cd270509b'
assert old_audit.count(b'#print axioms ') == 702
verify(root / owner_name, owner_sha)
prior = json.loads((prior_run / 'checked.json').read_text())
assert (prior['source_files'], prior['independent_reports'], prior['resource_and_component_probes']) == (6267, 297, 496)
assert len(prior['checks']) == 5 and all(item['exit'] == 0 and not item['diagnostics'] and not item['sorryAx'] and not item['nonstandard_axioms'] for item in prior['checks'])
verify(prior_archive / 'manifest.json', prior_manifest)
verify_prior_pins(prior_run / 'source-pins.json')
bound.add(prior_run / 'checked.json')
private_control = base / stage['private_control']
selected = json.loads((private_control / 'SELECTION.json').read_text())
private_run = base / stage['private_run']
assert selected['runtime'] == private_run.name
checked_path = private_run / 'checked.json'
checked = json.loads(checked_path.read_text())
receipt_path = work / stage['private_check_verified_receipt']
receipt = json.loads(receipt_path.read_text())
assert receipt['actual_session'] == stage['actual_private_session'] == 37551
assert receipt['actual_terminal'] and receipt['actual_terminal_exit'] == 0
assert receipt['checks'] == checked['checks'] and checked['all_six_components_checked'] and checked['proof_credit']
assert len(checked['checks']) == 6 and all(checked['passed'])
assert [item['name'] for item in checked['checks']] == stage['compile_order']
assert [item['total_axiom_reports'] for item in checked['checks']] == [2, 1, 1, 1, 1, 1]
assert checked['actual_new_public_axiom_reports'] == 7 and checked['actual_definition_declaration_checks'] == 0
assert checked['new_private_helpers_compiled_transitively'] == 6 and checked['fresh_credit_for_old_owner_theorems'] == 0
assert checked['all_selected_first_headers_exact'] and checked['all_three_old_owner_prefixes_byte_exact']
assert checked['limits'] == {'memory.max': '8589934592', 'memory.high': '8589934592', 'memory.swap.max': '0'}
verify_prior_pins(private_run / 'source-pins.json')
bound.update([checked_path, private_run / 'results.json', receipt_path])
for item in checked['checks']:
    bound.add(private_run / (item['name'] + '.txt'))
# Preserve rejected reports without giving their partial outputs proof credit.
for receipt_name, session in [('FIRST-CHECK-REJECTED.json', 29139),
                              ('SIX-SEED-FIRST-CHECK-REJECTED.json', 54344)]:
    rejected_path = work / receipt_name
    rejected = json.loads(rejected_path.read_text())
    failed_run = base / rejected['runtime']
    failed = json.loads((failed_run / 'results.json').read_text())
    assert rejected['actual_session'] == session and rejected['actual_terminal_exit'] == 1
    assert rejected['checks'] == failed['checks'] and not rejected['proof_credit'] and not failed['proof_credit']
    assert not (failed_run / 'checked.json').exists()
    if session == 29139:
        assert rejected['generated_sorryAx_public_report_rejected'] and failed['checks'][1]['sorryAx']
    else:
        assert rejected['checker_transitive_import_order_failure'] and not rejected['candidate_proof_bytes_changed']
    verify_prior_pins(failed_run / 'source-pins.json')
    bound.update([rejected_path, failed_run / 'results.json'])
    bound.update(failed_run / (item['name'] + '.txt') for item in failed['checks'])

chosen = {item['module']: item for item in selected['components']}
assert len(chosen) == 6
normal_sources = []
probes = []
public_names = []
definition_names = []
for item in expected:
    for key, value in chosen[item['module']].items():
        assert item[key] == value, (item['module'], key)
    packet = base / item['packet']
    verify(packet / 'MANIFEST.json', item['manifest_sha256'])
    for name, record in manifest_records(json.loads((packet / 'MANIFEST.json').read_text())):
        verify(packet / name, record)
    # The actual passed check parsed each dependency schema. Bind its exact artifact
    # and preserve historical old Node records instead of equating different raws.
    for pin_file in ['SOURCE-PINS.json', 'ADDITIONAL-SOURCE-PINS.json']:
        if (packet / pin_file).exists():
            verify_prior_pins(packet / pin_file)
    raw = verify(packet / item['source'], {'sha256': item['raw_sha256'], 'bytes': item['raw_bytes']})
    assert raw == (root / item['source_path']).read_bytes()
    declarations = raw
    if item['kind'] == 'existing_owner_EOF':
        before = prior_bytes(item['source_path'])
        assert len(before) == item['old_bytes'] and sha(before) == item['old_sha256']
        appended = verify(packet / item['append'], item['append_sha256'])
        assert raw == before + appended and item['append_offset'] == len(before)
        declarations = appended
    for header in item['headers']:
        assert verify(packet / header['file'], header['sha256']).rstrip(b'\n') in declarations
    probe = verify(packet / item['probe'], item['probe_sha256'])
    assert (private_run / 'source/MicroCFTA' / (item['module'] + '.lean')).read_bytes() == raw + b'\n' + probe
    assert re.findall(r'^private theorem (\w+)', declarations.decode(), re.M) == item['new_private_helper_names']
    assert re.findall(r'^private def (\w+)', declarations.decode(), re.M) == item['new_private_prop_names'] == []
    assert re.findall(r'^#print axioms (\S+)', probe.decode(), re.M) == item['names']
    assert probe.count(b'#print axioms ') == item['expected_axiom_reports']
    assert probe.count(b'#check ') == item['expected_declaration_checks'] == 0
    normal_sources.append(raw)
    probes.append(probe)
    public_names.extend(item['names'])
assert len(public_names) == len(set(public_names)) == 7 and not definition_names
assert sum(len(item['new_private_helper_names']) for item in expected) == 6
public = (work / 'PUBLIC-PROBES.lean.txt').read_bytes()
imports = (work / 'IMPORTS.lean.txt').read_bytes()
assert public == b''.join(probes)
assert imports == (control / 'EXPECTED-IMPORTS.lean.txt').read_bytes()
assert len(imports) == stage['old_audit_exact_offset'] == 195 and imports.count(b'import ') == 3
assert (root / audit_name).read_bytes() == imports + old_audit + b'\n' + public
assert sum(line.startswith(b'import ') for line in (root / audit_name).read_bytes().splitlines()) == 5270
assert (root / audit_name).read_bytes().count(b'#print axioms ') == 709
prior_independent = (prior_run / 'IndependentProbes.lean').read_bytes()
assert prior_independent.count(b'#print axioms ') == 297
for item in expected:
    imported = ('import MicroCFTA.' + item['module'] + '\n').encode()
    assert (imported in prior_independent) == (item['kind'] == 'existing_owner_EOF')
for name in ['strict-bind.py.txt', 'publication-driver.py.txt', 'shadow-compile.py.txt']:
    ast.parse((control / name).read_text())
normal_objects = root / 'lean/.lake/build/lib/lean/MicroCFTA'
assert normal_objects.is_dir()

# Root runs the mutation phase only after reviewing every preflight check.
runtime.mkdir()
objects = Path(tempfile.mkdtemp(prefix='mcfta-third-query-six-seed-publication-'))
(objects / 'MicroCFTA').mkdir()
modules = {item['module'] for item in expected}
for dependency in normal_objects.glob('*.olean'):
    if dependency.stem not in modules:
        (objects / 'MicroCFTA' / dependency.name).symlink_to(dependency)
(runtime / 'objects.json').write_text(json.dumps({'path': str(objects)}, indent=2) + '\n')
for item, raw, probe in zip(expected, normal_sources, probes):
    path = runtime / 'source/MicroCFTA' / (item['module'] + '.lean')
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(raw + b'\n' + probe)
    bound.add(path)
for source, target in [('strict-bind.py.txt', 'strict-new-and-bind.py'),
                       ('publication-driver.py.txt', 'check.py'), ('shadow-compile.py.txt', 'shadow-compile.py')]:
    (runtime / target).write_bytes((control / source).read_bytes())
(runtime / 'REPORT-BASE.json').write_bytes((control / 'REPORT-BASE.json').read_bytes())
(runtime / 'IndependentProbes.lean').write_bytes(imports + prior_independent + b'\n' + public)
(runtime / 'PUBLIC-PROBES.lean.txt').write_bytes(public)
selection = {
    'compile_order': stage['compile_order'],
    'definition_names': definition_names, 'prior_checkpoint': prior_commit,
    'prior_archive_manifest_sha256': prior_manifest,
    'prior_checked_sha256': sha((prior_run / 'checked.json').read_bytes()),
    'prior_pins_sha256': sha((prior_run / 'source-pins.json').read_bytes()),
    'baseline_sha256': sha(baseline_path.read_bytes()), 'stage_sha256': sha(stage_path.read_bytes()),
    'baseline_overrides': overrides,
    'override_digests': {name: sha((root / path).read_bytes()) for name, path in overrides.items()},
    'candidate_source_pins_use_owner_before_overrides': True, 'resource_owner_sha256': owner_sha,
    'prior_source_files': 6267, 'prior_combined_reports': 496, 'inherited_reports': 496,
    'fresh_reports': 7, 'combined_reports': 503, 'replaced_old_reports': 0,
    'new_theorem_declarations': 13, 'new_public_theorems': 7, 'new_private_theorems': 6,
    'new_prop_definitions': 0, 'new_definition_checks': 0, 'new_private_explicit_reports': 0,
    'owner_preflight_reports_fresh_this_batch': 0, 'resource_owner_reports_inherited': 264,
    'old_source_files_byte_exact': 6263, 'old_audit_offset': 195, 'new_audit_imports': 3,
    'actual_private_success': 37551, 'all_seven_selected_first_headers_exact': True,
    'all_three_old_owner_prefixes_byte_exact': True, 'fresh_credit_for_old_owner_theorems': 0,
    'all_new_formal_proof_checks_first_pass': False, 'axiom_strings_replayed': False,
}
(runtime / 'INHERITANCE-SELECTION.json').write_text(json.dumps(selection, indent=2) + '\n')
bound.update([Path(__file__), stage_path, baseline_path, work / 'IMPORTS.lean.txt',
              work / 'PUBLIC-PROBES.lean.txt', prior_run / 'IndependentProbes.lean'])
bound.update(current)
bound.update(path for path in runtime.iterdir() if path.is_file())
(runtime / 'source-pins.json').write_text(json.dumps({
    str(path.relative_to(root)): sha(path.read_bytes()) for path in sorted(bound)
}, indent=2, sort_keys=True) + '\n')
print(json.dumps({'run': str(runtime), 'gates': 5, 'strict_component_commands': 6,
    'fresh_public_reports': 7, 'definition_checks': 0, 'inherited_reports': 496,
    'combined_reports': 503, 'new_theorems': 13, 'new_private_explicit_reports': 0,
    'resource_owner_reports_fresh': 0, 'resource_owner_reports_inherited': 264,
    'source_files': 6270, 'independent_reports': 304, 'audit_reports': 709,
    'objects': str(objects)}))
