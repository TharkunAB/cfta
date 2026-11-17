from pathlib import Path
import ast
import hashlib
import json
import re
import tempfile

root = Path('/home/tritlo/Code/mcfta')
base = root / 'lean/restart-evidence'
control = base / '20261117-warm-no-new-mu-publication-control-draft'
work = base / '20261117-warm-no-new-mu-work'
assert Path(__file__).resolve().parent == work.resolve(), 'Root must review and copy this controller.'
assert Path(__file__).read_bytes() == (control / 'prepare-publication.py').read_bytes()
runtime = base / '20261117-warm-no-new-mu-publication'
assert not runtime.exists(), 'Preserve earlier runs.'
prior_run = base / '20261117-warm-semantic-finish-publication'
prior_archive = base / '20261117-warm-semantic-finish-checkpoint'
prior_commit = 'a59893a37d6c30b25a92f6ac499e5115057b9383'
prior_manifest = 'f75f1f825214e287d7d3957c8295408d90386072c77da65e357034e5feb52826'
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
    if isinstance(value, dict):
        return list(value.items())
    return [(item['path'], item) for item in value]


def manifest_records(manifest):
    if 'artifacts' in manifest:
        return [(item['path'], item) for item in manifest['artifacts']]
    return items(manifest['files'])


for name, record in json.loads((control / 'MANIFEST.json').read_text())['files'].items():
    verify(control / name, record)
bound.add(control / 'MANIFEST.json')
stage_path = work / 'SOURCES-NORMAL-STAGING.json'
stage = json.loads(stage_path.read_text())
assert stage == json.loads((control / 'EXPECTED-STAGE.json').read_text())
assert stage['prior_checkpoint'] == prior_commit
expected = stage['components']
overrides = {audit_name: str((work / 'Audit-BEFORE.lean.txt').relative_to(root))}
assert stage['baseline_overrides'] == overrides
assert (stage['source_files'], stage['audit_imports'], stage['audit_reports'],
        stage['independent_reports']) == (6267, 5267, 698, 293)
assert (stage['new_modules'], stage['new_public_theorems'], stage['new_private_helpers'],
        stage['new_theorem_declarations'], stage['new_prop_definitions']) == (3, 3, 46, 49, 4)
assert (stage['fresh_reports'], stage['inherited_reports'], stage['combined_reports']) == (3, 489, 492)
baseline_path = work / 'baseline-source-pins.json'
baseline = json.loads(baseline_path.read_text())
assert len(baseline) == 6264 and len(expected) == 3
new_names = {item['source_path'] for item in expected}
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
        digest = record['sha256'] if isinstance(record, dict) else record
        assert sha(data) == digest, name
        if isinstance(record, dict) and 'bytes' in record:
            assert len(data) == record['bytes'], name


for name, digest in baseline.items():
    assert sha(prior_bytes(name)) == digest, name
assert len(set(baseline) - {audit_name}) == 6263
old_audit = prior_bytes(audit_name)
assert len(old_audit) == stage['old_audit_bytes'] == 429545
assert sha(old_audit) == stage['old_audit_sha256'] == '12d45e499288075d0cb51f1d3f2243c0a88ae853cad71f6a7bf1782239ab1d00'
assert old_audit.count(b'#print axioms ') == 695
verify(root / owner_name, owner_sha)
prior = json.loads((prior_run / 'checked.json').read_text())
assert (prior['source_files'], prior['independent_reports'],
        prior['resource_and_component_probes']) == (6264, 290, 489)
assert len(prior['checks']) == 5 and all(item['exit'] == 0 and not item['diagnostics']
    and not item['sorryAx'] and not item['nonstandard_axioms'] for item in prior['checks'])
verify(prior_archive / 'manifest.json', prior_manifest)
verify_prior_pins(prior_run / 'source-pins.json')
bound.add(prior_run / 'checked.json')
def verify_candidate_pin(name, record):
    verify(root / name, record)


private_control = base / '20261117-warm-no-new-mu-alias-repair-check-control-draft'
selected = json.loads((private_control / 'SELECTION.json').read_text())
private_run = base / selected['runtime']
assert stage['private_run'] == selected['runtime']
checked_path = private_run / 'checked.json'
checked = json.loads(checked_path.read_text())
receipt_path = work / 'PRIVATE-CHECK-VERIFIED.json'
receipt = json.loads(receipt_path.read_text())
assert receipt['actual_session'] == 50959 and receipt['actual_terminal'] and receipt['actual_terminal_exit'] == 0
assert receipt['checks'] == checked['checks'] and checked['three_modules_checked']
assert len(checked['checks']) == 3 and all(checked['passed'])
assert checked['actual_public_axiom_reports'] == 3 and checked['actual_definition_declaration_checks'] == 0
assert checked['all_three_selected_first_headers_exact']
assert checked['private_helpers_compiled_transitively'] == 46
assert checked['private_prop_carrier_declaration_checks'] == 0
assert checked['limits'] == {'memory.max': '8589934592', 'memory.high': '8589934592', 'memory.swap.max': '0'}
verify_prior_pins(private_run / 'source-pins.json')
bound.update([checked_path, private_run / 'results.json', receipt_path])
for item in checked['checks']:
    bound.add(private_run / (item['name'] + '.txt'))
seen = set()
normal_sources = []
probes = []
public_names = []
definition_names = []
for item, chosen in zip(expected, selected['components']):
    for key, value in chosen.items():
        assert item[key] == value, (item['module'], key)
    packet = base / item['packet']
    manifest_path = packet / 'MANIFEST.json'
    verify(manifest_path, item['manifest_sha256'])
    if packet not in seen:
        seen.add(packet)
        for name, record in manifest_records(json.loads(manifest_path.read_text())):
            verify(packet / name, record)
        for pin_file in ['SOURCE-PINS.json', 'ADDITIONAL-SOURCE-PINS.json']:
            if (packet / pin_file).exists():
                for name, record in items(json.loads((packet / pin_file).read_text())):
                    verify_candidate_pin(name, record)
        if (packet / 'DEPENDENCY-PINS.json').exists():
            for name, record in items(json.loads((packet / 'DEPENDENCY-PINS.json').read_text())):
                verify(root / name, record)
                if isinstance(record, dict) and 'packet_manifest_sha256' in record:
                    verify((root / name).parent / 'MANIFEST.json', record['packet_manifest_sha256'])
        if (packet / 'FAILURE-PINS.json').exists():
            for record in json.loads((packet / 'FAILURE-PINS.json').read_text())['artifacts']:
                verify(root / record['path'], record)
    raw = verify(packet / item['source'], item['raw_sha256'])
    assert raw == (root / item['source_path']).read_bytes() and len(raw) == item['raw_bytes']
    header = verify(packet / item['header'], item['header_sha256'])
    assert header.rstrip(b'\n') in raw
    probe = verify(packet / item['probe'], item['probe_sha256'])
    assert (private_run / 'source/MicroCFTA' / (item['module'] + '.lean')).read_bytes() == raw + b'\n' + probe
    assert re.findall(r'^private theorem (\w+)', raw.decode(), re.M) == item['new_private_helper_names']
    assert re.findall(r'^private def (\w+)', raw.decode(), re.M) == item['new_private_prop_names']
    assert re.findall(r'^#print axioms (\S+)', probe.decode(), re.M) == item['names']
    assert probe.count(b'#print axioms ') == item['expected_axiom_reports']
    assert probe.count(b'#check ') == item['expected_declaration_checks']
    normal_sources.append(raw)
    probes.append(probe)
    public_names.extend(item['names'])
assert len(public_names) == len(set(public_names)) == 3 and not definition_names
assert sum(len(item['new_private_helper_names']) for item in expected) == 46
assert sum(len(item['new_private_prop_names']) for item in expected) == 4
failed_run = base / '20261117-warm-no-new-mu-three-module-check'
failed = json.loads((failed_run / 'results.json').read_text())
rejected_path = work / 'THREE-MODULE-FIRST-CHECK-REJECTED.json'
rejected = json.loads(rejected_path.read_text())
assert rejected['actual_session'] == 78575 and rejected['actual_terminal_exit'] == 1
assert rejected['checks'] == failed['checks'] and not failed['proof_credit']
assert [item['exit'] for item in failed['checks']] == [1, 1, 1]
assert [item['diagnostics'] for item in failed['checks']] == [3, 1, 1]
assert failed['checks'][0]['sorryAx'] and 'sorryAx' in failed['checks'][0]['nonstandard_axioms']
assert failed['private_helpers_compiled_transitively'] == 0
assert rejected['generated_sorryAx_report_rejected']
assert not (failed_run / 'checked.json').exists()
bound.update([failed_run / 'results.json', rejected_path])
bound.update(failed_run / (item['name'] + '.txt') for item in failed['checks'])
public = (work / 'PUBLIC-PROBES.lean.txt').read_bytes()
imports = (work / 'IMPORTS.lean.txt').read_bytes()
assert public == b''.join(probes)
assert imports == ''.join('import MicroCFTA.' + item['module'] + '\n' for item in expected).encode()
assert len(imports) == stage['old_audit_exact_offset'] == 189
assert (root / audit_name).read_bytes() == imports + old_audit + b'\n' + public
assert sum(line.startswith(b'import ') for line in (root / audit_name).read_bytes().splitlines()) == 5267
assert (root / audit_name).read_bytes().count(b'#print axioms ') == 698
prior_independent = (prior_run / 'IndependentProbes.lean').read_bytes()
assert prior_independent.count(b'#print axioms ') == 290
for item in expected:
    assert ('import MicroCFTA.' + item['module'] + '\n').encode() not in prior_independent
for name in ['strict-bind.py.txt', 'publication-driver.py.txt', 'shadow-compile.py.txt']:
    ast.parse((control / name).read_text())
normal_objects = root / 'lean/.lake/build/lib/lean/MicroCFTA'
assert normal_objects.is_dir()

# Root runs the mutation phase only after reviewing every preflight check.
runtime.mkdir()
objects = Path(tempfile.mkdtemp(prefix='mcfta-warm-no-new-mu-publication-'))
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
    'compile_order': [item['module'] for item in expected],
    'definition_names': definition_names, 'prior_checkpoint': prior_commit,
    'prior_archive_manifest_sha256': prior_manifest,
    'prior_checked_sha256': sha((prior_run / 'checked.json').read_bytes()),
    'prior_pins_sha256': sha((prior_run / 'source-pins.json').read_bytes()),
    'baseline_sha256': sha(baseline_path.read_bytes()), 'stage_sha256': sha(stage_path.read_bytes()),
    'baseline_overrides': overrides,
    'override_digests': {name: sha((root / path).read_bytes()) for name, path in overrides.items()},
    'candidate_source_pins_need_no_override': True, 'resource_owner_sha256': owner_sha,
    'prior_source_files': 6264, 'prior_combined_reports': 489, 'inherited_reports': 489,
    'fresh_reports': 3, 'combined_reports': 492, 'replaced_old_reports': 0,
    'new_theorem_declarations': 49, 'new_public_theorems': 3, 'new_private_theorems': 46,
    'new_prop_definitions': 4, 'new_definition_checks': 0, 'new_private_explicit_reports': 0,
    'owner_preflight_reports_fresh_this_batch': 0, 'resource_owner_reports_inherited': 264,
    'old_source_files_byte_exact': 6263, 'old_audit_offset': 189, 'new_audit_imports': 3,
    'failed_attempts_preserved': [78575], 'actual_private_success': 50959,
    'all_three_selected_first_headers_exact': True, 'checked_alias_only_repair': True,
    'failed_generated_sorryAx_report_rejected': True, 'axiom_strings_replayed': False,
}
(runtime / 'INHERITANCE-SELECTION.json').write_text(json.dumps(selection, indent=2) + '\n')
bound.update([Path(__file__), stage_path, baseline_path, work / 'IMPORTS.lean.txt',
              work / 'PUBLIC-PROBES.lean.txt', prior_run / 'IndependentProbes.lean'])
bound.update(current)
bound.update(path for path in runtime.iterdir() if path.is_file())
(runtime / 'source-pins.json').write_text(json.dumps({
    str(path.relative_to(root)): sha(path.read_bytes()) for path in sorted(bound)
}, indent=2, sort_keys=True) + '\n')
print(json.dumps({'run': str(runtime), 'gates': 5, 'strict_modules': 3,
    'fresh_public_reports': 3, 'definition_checks': 0, 'inherited_reports': 489,
    'combined_reports': 492, 'new_theorems': 49, 'new_private_explicit_reports': 0,
    'resource_owner_reports_fresh': 0, 'resource_owner_reports_inherited': 264,
    'source_files': 6267, 'independent_reports': 293, 'audit_reports': 698,
    'objects': str(objects)}))
