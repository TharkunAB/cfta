from pathlib import Path
import ast
import hashlib
import json
import re
import subprocess
import tempfile

root = Path('/home/tritlo/Code/mcfta')
base = root / 'lean/restart-evidence'
control = base / '20261118-retained-source-gate-skip-publication-control-draft'
stage_control = base / '20261118-retained-source-gate-skip-staging-control-draft'
work = base / '20261118-retained-source-gate-skip-work'
runtime = base / '20261118-retained-source-gate-skip-publication'
prior_work = base / '20261117-numerical-source-callbacks-work'
prior_run = base / '20261117-numerical-seed-closure-publication'
prior_archive = base / '20261118-actual-query-sequence-seeds-checkpoint'
source_commit = '1a3de82aec4bab8cc6b21012103e6311a951b266'
assert Path(__file__).resolve().parent == work.resolve()
assert Path(__file__).read_bytes() == (control / 'prepare-publication.py').read_bytes()
assert not runtime.exists(), 'Preserve all earlier runtimes.'
sha = lambda data: hashlib.sha256(data).hexdigest()
bound = set()

def verify(path, record):
    data = path.read_bytes()
    assert sha(data) == (record['sha256'] if isinstance(record, dict) else record), str(path)
    if isinstance(record, dict) and 'bytes' in record:
        assert len(data) == record['bytes'], str(path)
    bound.add(path)
    return data

for name, record in json.loads((control / 'MANIFEST.json').read_text())['files'].items():
    verify(control / name, record)
bound.add(control / 'MANIFEST.json')
for name, record in json.loads((control / 'ACTUAL-INPUT-PINS.json').read_text()).items():
    verify(root / name, record)
for name, record in json.loads((stage_control / 'MANIFEST.json').read_text())['files'].items():
    verify(stage_control / name, record)
bound.add(stage_control / 'MANIFEST.json')
stage_bytes = (work / 'SOURCES-NORMAL-STAGING.json').read_bytes()
assert stage_bytes == (control / 'EXPECTED-STAGE.json').read_bytes()
stage = json.loads(stage_bytes)
assert stage['status'] == 'ACTUALLY STAGED BY ROOT AFTER VERIFIED TERMINAL PASS'
assert stage['source_baseline'] == source_commit and stage['normal_Source_changed'] and not stage['published']
assert (stage['source_files'], stage['audit_imports'], stage['audit_reports'], stage['independent_reports']) == (6279, 5279, 726, 321)
assert (stage['fresh_reports'], stage['inherited_reports'], stage['combined_reports']) == (2, 518, 520)
assert stage['owner_preflight_reports_fresh_this_batch'] == 0 and stage['resource_owner_reports_inherited'] == 264
bound.add(work / 'SOURCES-NORMAL-STAGING.json')
overrides = stage['baseline_overrides']
assert set(overrides) == {'lean/MicroCFTA/Audit.lean', 'lean/MicroCFTA/SourceSynthesisCurrentRootEmptyCheckGate.lean'}

def historical(name, record):
    # Only the Gate owner and Audit changed. Their exact old bytes are past data.
    return verify(root / overrides.get(name, name), record)

private_control = base / stage['private_control']
verify(private_control / 'MANIFEST.json', stage['private_control_manifest_sha256'])
selected_bytes = verify(private_control / 'SELECTION.json', stage['private_selection_sha256'])
assert selected_bytes == (control / 'CHECK-SELECTION.json').read_bytes()
selected = json.loads(selected_bytes)
assert selected['compile_order'] == stage['compile_order'] and len(selected['components']) == 2
private_run = base / stage['private_run']
receipt_path = work / stage['private_verified_receipt']
receipt = json.loads(verify(receipt_path, stage['private_receipt_sha256']))
assert receipt['actual_terminal'] and receipt['actual_terminal_exit'] == 0
assert receipt['actual_session'] == 15994 and receipt['source_baseline'] == source_commit
checked = json.loads(verify(private_run / 'checked.json', receipt['checked_sha256']))
assert json.loads(verify(private_run / 'results.json', receipt['results_sha256'])) == checked
assert receipt['checks'] == checked['checks'] and len(checked['checks']) == 2 and all(checked['passed'])
assert checked['proof_credit'] and checked['both_selected_FIRST_headers_exact']
assert checked['actual_printed_public_axiom_reports'] == 2 and checked['actual_definition_declaration_checks'] == 0
assert checked['limits'] == {'memory.max': '8589934592', 'memory.high': '8589934592', 'memory.swap.max': '0'}
assert [item['name'] for item in checked['checks']] == selected['compile_order']
assert all(item['exit'] == 0 and item['total_axiom_reports'] == 1 and not item['diagnostics']
    and not item['sorryAx'] and not item['nonstandard_axioms'] for item in checked['checks'])
private_pins = json.loads(verify(private_run / 'source-pins.json', receipt['source_pins_sha256']))
assert len(private_pins) == receipt['pins_independently_reverified'] == 6338
for name, record in private_pins.items():
    historical(name, record)
bound.update(private_run / (item['name'] + '.txt') for item in checked['checks'])
baseline_path = work / 'baseline-source-pins.json'
baseline = json.loads(baseline_path.read_text())
assert len(baseline) == 6278
for name, record in baseline.items():
    historical(name, record)
new_source = 'lean/MicroCFTA/SourceSynthesisCurrentRetainedSharedEmptySkip.lean'
assert new_source not in baseline
current = sorted((root / 'lean/MicroCFTA').glob('*.lean'))
assert {str(path.relative_to(root)) for path in current} == set(baseline) | {new_source}
assert len(set(baseline) - set(overrides)) == 6276
# Bind the actual prior Source publication and the pushed immutable checkpoint.
push = json.loads((prior_work / 'PUSH-VERIFIED.json').read_text())
prior_source = json.loads((prior_work / 'SOURCE-COMMIT.json').read_text())
prior_publication = json.loads((prior_work / 'PUBLICATION-VERIFIED.json').read_text())
assert push['source_commit'] == prior_source['source_commit'] == source_commit
assert push['checkpoint_commit'] == push['remote_commit']
assert push['actual_push_terminal'] and push['actual_push_terminal_exit'] == 0
assert push['actual_remote_check_terminal'] and push['actual_remote_check_terminal_exit'] == 0
assert push['postpush_current_tree_verifier_terminal_exit'] == 0
assert prior_source['actual_terminal'] and prior_source['actual_terminal_exit'] == 0
assert prior_publication['actual_terminal'] and prior_publication['actual_terminal_exit'] == 0
assert prior_publication['actual_session'] == prior_source['publication_actual_session'] == 10938
assert [x['total_axiom_reports'] for x in prior_publication['checks']] == [724, 15, 319, 724, 724]
assert prior_publication['combined_reports'] == 518 and prior_publication['resource_reports_inherited'] == 264
verify(prior_archive / 'manifest.json', push['archive_manifest_sha256'])
subprocess.run(['git', 'merge-base', '--is-ancestor', push['checkpoint_commit'], 'HEAD'], cwd=root, check=True)
prior_checked = json.loads((prior_run / 'checked.json').read_text())
assert prior_checked['all_five_gates_passed']
assert (prior_checked['source_files'], prior_checked['independent_reports'], prior_checked['resource_and_component_probes']) == (6278, 319, 518)
for name, digest in json.loads((prior_run / 'source-pins.json').read_text()).items():
    historical(name, digest)
bound.update([prior_work / 'PUSH-VERIFIED.json', prior_work / 'SOURCE-COMMIT.json',
    prior_work / 'PUBLICATION-VERIFIED.json', prior_work / 'PUBLICATION-ACTUAL-RUN.json',
    prior_run / 'checked.json', prior_run / 'source-pins.json', prior_run / 'IndependentProbes.lean',
    prior_archive / 'manifest.json', prior_archive / 'verify.py', prior_archive / 'archived-inputs.json'])
raw_sources = {}
public = b''
for item, original in zip(stage['components'], selected['components']):
    assert all(item[key] == value for key, value in original.items())
    packet = base / item['packet']
    manifest = json.loads(verify(packet / 'MANIFEST.json', item['manifest_sha256']))
    for name, record in manifest['files'].items():
        verify(packet / name, record)
    for name in ['SOURCE-PINS.json', 'DEPENDENCY-PINS.json']:
        if (packet / name).exists():
            for path, record in json.loads((packet / name).read_text()).items():
                historical(path, record)
    raw = verify(root / item['source_path'], {'sha256': item['raw_sha256'], 'bytes': item['raw_bytes']})
    assert raw == (packet / item['source']).read_bytes()
    declarations = raw
    if item['kind'] == 'existing_owner_EOF':
        before = verify(root / item['old_snapshot'], {'sha256': item['owner_sha256'], 'bytes': item['owner_bytes']})
        declarations = verify(packet / item['append'], item['append_sha256'])
        assert raw == before + declarations
    assert b'#print axioms ' not in raw and b'#check ' not in raw
    assert not re.search(rb'set_option\s+(maxHeartbeats|maxRecDepth|warningAsError|linter\.)', declarations)
    assert not re.findall(rb'^private theorem ', declarations, re.M)
    assert not re.findall(rb'^private def ', declarations, re.M)
    header = verify(packet / item['header'], item['header_sha256'])
    start = raw.index(header.splitlines()[0])
    assert raw[start:raw.index(b' := by', start)].rstrip() == header.rstrip()
    probe = verify(packet / item['probe'], item['probe_sha256'])
    assert (private_run / 'source/MicroCFTA' / (item['module'] + '.lean')).read_bytes() == raw + b'\n' + probe
    bound.add(private_run / 'source/MicroCFTA' / (item['module'] + '.lean'))
    raw_sources[item['module']] = raw
    public += probe
assert public == (work / 'PUBLIC-PROBES.lean.txt').read_bytes() == (control / 'EXPECTED-PUBLIC-PROBES.lean.txt').read_bytes()
assert public.count(b'#print axioms ') == 2 and b'#check ' not in public
imports = (work / 'IMPORTS.lean.txt').read_bytes()
assert imports == (control / 'EXPECTED-IMPORTS.lean.txt').read_bytes() and len(imports) == 63
old_audit = verify(root / overrides['lean/MicroCFTA/Audit.lean'], {'sha256': stage['old_audit_sha256'], 'bytes': stage['old_audit_bytes']})
assert old_audit.count(b'#print axioms ') == 724
assert (root / 'lean/MicroCFTA/Audit.lean').read_bytes() == imports + old_audit + b'\n' + public
assert (root / 'lean/MicroCFTA/Audit.lean').read_bytes().count(b'#print axioms ') == 726
assert sum(line.startswith(b'import ') for line in (root / 'lean/MicroCFTA/Audit.lean').read_bytes().splitlines()) == 5279
prior_independent = (prior_run / 'IndependentProbes.lean').read_bytes()
assert prior_independent.count(b'#print axioms ') == 319 and imports not in prior_independent
owner_name = 'lean/MicroCFTA/SourcePruningEnumerationSharedEagerReservation.lean'
owner_sha = sha((root / owner_name).read_bytes())
assert owner_sha == baseline[owner_name]
for name in ['strict-bind.py.txt', 'publication-driver.py.txt', 'shadow-compile.py.txt']:
    ast.parse((control / name).read_text())
normal_objects = root / 'lean/.lake/build/lib/lean/MicroCFTA'
assert normal_objects.is_dir()
# Root executes this phase after every read-only preflight passes.
runtime.mkdir()
objects = Path(tempfile.mkdtemp(prefix='mcfta-retained-source-gate-skip-publication-'))
(objects / 'MicroCFTA').mkdir()
for dependency in normal_objects.glob('*.olean'):
    if dependency.stem not in raw_sources:
        (objects / 'MicroCFTA' / dependency.name).symlink_to(dependency)
(runtime / 'objects.json').write_text(json.dumps({'path': str(objects)}, indent=2) + '\n')
for module, raw in raw_sources.items():
    path = runtime / 'source/MicroCFTA' / (module + '.lean')
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(raw)
    bound.add(path)
fresh_imports = ''.join('import MicroCFTA.' + module + '\n' for module in selected['compile_order']).encode()
(runtime / 'FreshPublicProbes.lean').write_bytes(fresh_imports + public)
(runtime / 'IndependentProbes.lean').write_bytes(imports + prior_independent + b'\n' + public)
for src, dst in [('strict-bind.py.txt', 'strict-new-and-bind.py'), ('publication-driver.py.txt', 'check.py'), ('shadow-compile.py.txt', 'shadow-compile.py')]:
    (runtime / dst).write_bytes((control / src).read_bytes())
(runtime / 'REPORT-BASE.json').write_bytes((control / 'REPORT-BASE.json').read_bytes())
inheritance = {
    'compile_order': selected['compile_order'], 'definition_names': [],
    'prior_checkpoint': push['checkpoint_commit'], 'prior_archive_manifest_sha256': push['archive_manifest_sha256'],
    'prior_checked_sha256': sha((prior_run / 'checked.json').read_bytes()),
    'prior_pins_sha256': sha((prior_run / 'source-pins.json').read_bytes()),
    'stage_sha256': sha(stage_bytes), 'baseline_sha256': sha(baseline_path.read_bytes()),
    'baseline_overrides': overrides,
    'override_digests': {name: sha((root / path).read_bytes()) for name, path in overrides.items()},
    'inherited_reports': 518, 'fresh_reports': 2, 'combined_reports': 520,
    'resource_owner_sha256': owner_sha, 'resource_owner_reports_inherited': 264,
    'owner_preflight_reports_fresh_this_batch': 0, 'new_private_helpers': 0,
    'Prop_declaration_checks': 0, 'Prop_axiom_credit': 0,
    'actual_private_session': 15994, 'private_receipt_sha256': sha(receipt_path.read_bytes()),
    'fresh_owner_theorem_credit': 0, 'cache_data_copied': False,
}
(runtime / 'INHERITANCE-SELECTION.json').write_text(json.dumps(inheritance, indent=2) + '\n')
bound.update([Path(__file__), baseline_path, work / 'PUBLIC-PROBES.lean.txt', work / 'IMPORTS.lean.txt'])
bound.update(current)
bound.update(path for path in runtime.iterdir() if path.is_file())
(runtime / 'source-pins.json').write_text(json.dumps({str(path.relative_to(root)): sha(path.read_bytes()) for path in sorted(bound)}, indent=2, sort_keys=True) + '\n')
print(json.dumps({'runtime': str(runtime), 'gates': 5, 'strict_fresh_modules': 2,
    'fresh_public_reports': 2, 'definition_checks': 0, 'inherited_reports': 518,
    'combined_reports': 520, 'source_files': 6279, 'independent_reports': 321,
    'audit_reports': 726, 'objects': str(objects), 'normal_Source_changed': False}))
