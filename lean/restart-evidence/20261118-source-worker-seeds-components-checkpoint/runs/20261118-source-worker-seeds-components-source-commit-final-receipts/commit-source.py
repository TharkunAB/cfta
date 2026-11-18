from pathlib import Path
import datetime
import hashlib
import json
import subprocess

ROOT = Path('/home/tritlo/Code/mcfta')
BASE = ROOT / 'lean/restart-evidence'
CONTROL = BASE / '20261118-source-worker-seeds-components-source-commit-final-receipts'
WORK = BASE / '20261118-source-worker-seeds-components-work'
assert Path(__file__).resolve().parent == WORK.resolve(), 'Root must review and copy this controller.'
assert Path(__file__).read_bytes() == (CONTROL / 'commit-source.py').read_bytes()
SHA = lambda data: hashlib.sha256(data).hexdigest()
GIT = lambda *args: subprocess.check_output(['git', *args], cwd=ROOT)
PARENT = '7dd87b6642d3114e1d02713af04a5ed494f72059'
MESSAGE = 'Preserve worker query resources across preparation phases'
FILES = [
    'lean/MicroCFTA/SourceCurrentNativeNumericalSeedClosure.lean',
    'lean/MicroCFTA/SourcePruningEnumerationSelectedPreparationNoNewMu.lean',
    'lean/MicroCFTA/SourcePruningEnumerationSharedIncomingQueryEventResources.lean',
    'lean/MicroCFTA/SourcePruningEnumerationSelectedPrefixNarrowNoNewMu.lean',
    'lean/MicroCFTA/SourcePruningEnumerationSharedDispatchQueryEventResources.lean',
    'lean/MicroCFTA/Audit.lean',
]
for name, record in json.loads((CONTROL / 'MANIFEST.json').read_text())['files'].items():
    data = (CONTROL / name).read_bytes()
    assert SHA(data) == record['sha256'] and len(data) == record['bytes'], name
for name, record in json.loads((CONTROL / 'SOURCE-PINS.json').read_text()).items():
    data = (ROOT / name).read_bytes()
    assert SHA(data) == record['sha256'] and len(data) == record['bytes'], name
assert not (WORK / 'SOURCE-COMMIT.json').exists()
stage = json.loads((WORK / 'SOURCES-NORMAL-STAGING.json').read_text())
assert {item['source_path'] for item in stage['components']} | {'lean/MicroCFTA/Audit.lean'} == set(FILES)
assert len(stage['components']) == 5
assert (stage['source_files'], stage['audit_imports'], stage['audit_reports'], stage['independent_reports']) == (6283, 5283, 733, 328)
assert (stage['fresh_reports'], stage['inherited_reports'], stage['combined_reports']) == (7, 520, 527)
assert stage['new_public_theorems'] == stage['new_private_helpers_transitive'] == 7
assert stage['new_Prop_definitions'] == stage['definition_checks'] == stage['explicit_private_reports'] == 0
assert stage['resource_owner_reports_inherited'] == 264 and stage['fresh_credit_for_old_owner_theorems'] == 0
push = json.loads((ROOT / stage['prior_checkpoint_push_receipt']).read_text())
assert push['checkpoint_commit'] == push['remote_commit'] == PARENT
assert push['source_commit'] == stage['source_baseline'] == 'fc345af6e51dd1e813fed83423f25c3228b78874'
assert push['actual_push_terminal_exit'] == push['actual_remote_check_terminal_exit'] == 0
assert push['postpush_current_tree_verifier_terminal_exit'] == 0
overrides = stage['baseline_overrides']
new_sources = {item['source_path'] for item in stage['components'] if item['kind'] == 'new_module'}
assert len(new_sources) == 4 and set(overrides) == set(FILES) - new_sources
baseline = json.loads((WORK / 'baseline-source-pins.json').read_text())
assert len(baseline) == 6279 and len(set(baseline) - set(overrides)) == 6277
for name, digest in baseline.items():
    assert SHA((ROOT / overrides.get(name, name)).read_bytes()) == digest, name
assert {str(p.relative_to(ROOT)) for p in (ROOT / 'lean/MicroCFTA').glob('*.lean')} == set(baseline) | new_sources
private_sessions = []
for subset, session, reports, pin_count in zip(stage['private_subsets'], [23742, 33636], [5, 2], [6477, 6360]):
    private = BASE / subset['runtime']
    receipt = json.loads((ROOT / subset['verified_receipt']).read_text())
    checked = json.loads((private / 'checked.json').read_text())
    assert receipt['actual_session'] == session
    assert receipt['actual_terminal'] and receipt['actual_terminal_exit'] == 0
    assert receipt['checks'] == checked['checks'] and all(checked['passed']) and checked['proof_credit']
    assert sum(item['total_axiom_reports'] for item in checked['checks']) == reports
    assert all(item['exit'] == 0 and not item['diagnostics'] and not item['sorryAx']
        and not item['nonstandard_axioms'] and item['declaration_checks'] == 0 for item in checked['checks'])
    pins = json.loads((private / 'source-pins.json').read_text())
    assert len(pins) == receipt['pins_independently_reverified'] == pin_count
    for name, digest in pins.items():
        assert SHA((ROOT / overrides.get(name, name)).read_bytes()) == digest, name
    private_sessions.append(session)

# Final actual publication receipts are required. No transient receipt hash is pinned.
publication = BASE / '20261118-source-worker-seeds-components-publication'
actual = json.loads((WORK / 'PUBLICATION-ACTUAL-RUN.json').read_text())
verified = json.loads((WORK / 'PUBLICATION-VERIFIED.json').read_text())
published = json.loads((publication / 'checked.json').read_text())
assert actual['actual_terminal'] and actual['actual_terminal_exit'] == 0
assert verified['actual_terminal'] and verified['actual_terminal_exit'] == 0
assert verified['runtime'] == actual['runtime'] == publication.name
assert type(verified['actual_session']) is int and verified['actual_session'] > 0
assert verified['actual_session'] == actual['actual_session']
assert verified['checks'] == published['checks']
assert json.loads((publication / 'results.json').read_text()) == published
assert verified['checked_sha256'] == SHA((publication / 'checked.json').read_bytes())
assert verified['source_pins_sha256'] == SHA((publication / 'source-pins.json').read_bytes())
checks = published['checks']
assert len(checks) == 5
assert [item['name'] for item in checks] == ['public-build',
    'strict-new-components-and-prior-bindings', 'independent-imports', 'audit-build', 'audit-strict']
assert all(item['exit'] == 0 and not item['diagnostics'] and not item['sorryAx']
    and not item['nonstandard_axioms'] and item['declaration_checks'] == 0 for item in checks)
assert [item['total_axiom_reports'] for item in checks] == [733, 7, 328, 733, 733]
assert checks[1]['axiom_groups'] == 7 and checks[1]['axiom_free_reports'] == 0
assert checks[2]['axiom_groups'] == 325 and checks[2]['axiom_free_reports'] == 3
assert checks[4]['axiom_groups'] == 727 and checks[4]['axiom_free_reports'] == 6
assert published['all_five_gates_passed'] and published['source_pins_unchanged']
assert (published['source_files'], published['direct_audit_imports'], published['individual_reports'], published['independent_reports']) == (6283, 5283, 733, 328)
assert (published['fresh_reports'], published['inherited_reports'], published['combined_reports']) == (7, 520, 527)
assert published['new_public_theorems'] == published['new_private_theorems'] == 7
assert published['new_theorem_declarations'] == 14 and published['new_prop_definitions'] == 0
assert published['resource_owner_reports_inherited'] == 264 and published['owner_preflight_reports_fresh_this_batch'] == 0
assert published['resource_admitted_request_Seeds_component_checked']
assert published['selected_preparation_original_fuel_Seeds_component_checked']
assert published['actual_incoming_event_resource_component_checked']
assert published['source_qualified_original_fuel_narrowing_checked']
assert published['same_actual_dispatch_event_resources_checked']
assert published['original_narrowing_FIRST_preserved'] and not published['original_narrowing_FIRST_byte_equal']
assert not published['original_narrowing_FIRST_alpha_equivalent']
assert not published['current_equals_legacy_premise_added']
assert not published['all_original_eager_worker_query_admissions_proved']
assert not published['native_inhabitance_proved'] and not published['joint_finite_completion_proved'] and not published['haskell_changed']
assert type(published['audited_theorems']) is int and published['audited_theorems'] > 0
assert published['audited_theorems'] == verified['audited_theorems']
pub_pins = json.loads((publication / 'source-pins.json').read_text())
assert verified['pins_independently_reverified'] == len(pub_pins)
for name, digest in pub_pins.items():
    assert SHA((ROOT / name).read_bytes()) == digest, name
for item in stage['components']:
    packet = BASE / item['packet']
    assert SHA((packet / 'MANIFEST.json').read_bytes()) == item['manifest_sha256']
    current = (ROOT / item['source_path']).read_bytes()
    assert current == (packet / item['source']).read_bytes() and SHA(current) == item['raw_sha256']
    if item['kind'] == 'existing_owner_import_and_EOF':
        before = (ROOT / item['old_snapshot']).read_bytes()
        prefix = (packet / item['imports']).read_bytes()
        appended = (packet / item['append']).read_bytes()
        assert len(before) == 23529 and len(prefix) == item['owner_offset'] == 61
        assert SHA(before) == item['owner_sha256'] and current == prefix + before + appended
    for header in item['headers']:
        data = (packet / header['file']).read_bytes()
        assert SHA(data) == header['sha256']
        start = current.index(data.splitlines()[0])
        assert current[start:current.index(b':= by', start)].rstrip() == data.rstrip()
    probe = (packet / item['probe']).read_bytes()
    assert SHA(probe) == item['probe_sha256']
old_audit = (WORK / 'Audit-BEFORE.lean.txt').read_bytes()
public_probes = (WORK / 'PUBLIC-PROBES.lean.txt').read_bytes()
imports = (WORK / 'IMPORTS.lean.txt').read_bytes()
assert len(old_audit) == 434278 and len(imports) == 287 and imports.count(b'import ') == 4
assert old_audit.count(b'#print axioms ') == 726 and public_probes.count(b'#print axioms ') == 7
assert (ROOT / 'lean/MicroCFTA/Audit.lean').read_bytes() == imports + old_audit + b'\n' + public_probes
assert GIT('branch', '--show-current').decode().strip() == 'formalize'
assert GIT('rev-parse', 'HEAD').decode().strip() == PARENT
assert not GIT('diff', '--cached', '--name-only')
assert set(GIT('diff', '--name-only', 'HEAD').decode().splitlines()) == set(FILES) - new_sources
for name in new_sources:
    assert not GIT('ls-files', '--', name), name
source_bytes = {name: (ROOT / name).read_bytes() for name in FILES}
assert all(not (ROOT / name).is_symlink() for name in FILES)

# Root explicitly approves and executes this exact six-file Source commit.
subprocess.run(['git', 'add', '-f', '--', *FILES], check=True, cwd=ROOT)
assert set(GIT('diff', '--cached', '--name-only').decode().splitlines()) == set(FILES)
for name, data in source_bytes.items():
    assert GIT('show', ':' + name) == data, name
subprocess.run(['git', 'diff', '--cached', '--check'], check=True, cwd=ROOT)
subprocess.run(['git', 'commit', '--quiet', '-m', MESSAGE], check=True, cwd=ROOT)
head = GIT('rev-parse', 'HEAD').decode().strip()
assert GIT('rev-parse', head + '^').decode().strip() == PARENT
assert set(GIT('diff-tree', '--no-commit-id', '--name-only', '-r', head).decode().splitlines()) == set(FILES)
assert not GIT('status', '--porcelain', '--untracked-files=no')
receipt = {'at': datetime.datetime.now().astimezone().isoformat(), 'source_commit': head,
    'parent': PARENT, 'files': FILES, 'actual_terminal': True, 'actual_terminal_exit': 0,
    'message': MESSAGE, 'private_actual_sessions': private_sessions,
    'publication_actual_session': verified['actual_session'],
    'audited_theorems': published['audited_theorems'],
    'source_files': 6283, 'audit_imports': 5283, 'audit_reports': 733,
    'independent_reports': 328, 'fresh_public_reports': 7, 'inherited_reports': 520,
    'combined_reports': 527, 'new_public_theorems': 7, 'new_private_theorems': 7,
    'new_definitions': 0, 'resource_reports_inherited': 264,
    'old_seed_closure_owner_bytes': 23529, 'old_seed_closure_owner_offset': 61,
    'old_audit_contiguous_bytes': 434278, 'old_audit_offset': 287,
    'selected_public_FIRST_headers_checked': True,
    'original_narrowing_FIRST_preserved': True, 'original_narrowing_FIRST_byte_equal': False,
    'original_narrowing_FIRST_alpha_equivalent': False,
    'all_original_eager_worker_query_admissions_proved': False,
    'native_inhabitance_proved': False, 'guard_truth_proved': False,
    'joint_finite_completion_proved': False, 'haskell_changed': False}
(WORK / 'SOURCE-COMMIT.json').write_text(json.dumps(receipt, indent=2) + '\n')
print(json.dumps(receipt))
