from pathlib import Path
import datetime
import hashlib
import json
import re
import subprocess

ROOT = Path('/home/tritlo/Code/mcfta')
BASE = ROOT/'lean/restart-evidence'
CONTROL = BASE/'20261118-terminal-and-query-seeds-source-commit-control-draft'
WORK = BASE/'20261118-terminal-query-resources-work'
PARENT = 'e5fc00c2a9ccf70322b4f0a2780e1293ecb2ead9'
MESSAGE = 'Preserve source invariants through terminal and dispatch queries'
OLD_FILES = ['lean/MicroCFTA/SourcePruningEnumerationSharedTerminalQueryEvents.lean', 'lean/MicroCFTA/Audit.lean']
NEW_FILE = 'lean/MicroCFTA/SourcePruningEnumerationSharedIncomingQuerySeeds.lean'
FILES = [OLD_FILES[0], NEW_FILE, OLD_FILES[1]]
assert Path(__file__).resolve().parent == WORK.resolve(), 'Root reviews and copies this exact controller.'
assert Path(__file__).read_bytes() == (CONTROL/'commit-source.py').read_bytes()
SHA = lambda data: hashlib.sha256(data).hexdigest()
GIT = lambda *args: subprocess.check_output(['git', *args], cwd=ROOT)


def verify(path, record):
    data = path.read_bytes()
    assert SHA(data) == (record['sha256'] if isinstance(record, dict) else record), str(path)
    if isinstance(record, dict) and 'bytes' in record:
        assert len(data) == record['bytes'], str(path)
    return data


def records(manifest):
    files = manifest['files']
    return files.items() if isinstance(files, dict) else [(r.get('file', r.get('path')), r) for r in files]


for name, record in records(json.loads((CONTROL/'MANIFEST.json').read_text())):
    verify(CONTROL/name, record)
for name, record in json.loads((CONTROL/'SOURCE-PINS.json').read_text()).items():
    verify(ROOT/name, record)
assert not (WORK/'SOURCE-COMMIT.json').exists()
stage = json.loads((WORK/'SOURCES-NORMAL-STAGING.json').read_text())
assert stage['status'] == 'SOURCE_NORMAL_STAGING_COMPLETED' and stage['normal_Source_changed']
assert set(stage['exact_Source_write_paths']) == set(FILES)
assert set(stage['baseline_overrides']) == set(OLD_FILES)
assert len(stage['components']) == 2 and stage['new_modules'] == stage['existing_owners_changed'] == 1
assert stage['actual_private_sessions'] == [99821, 69321, 32584]
assert stage['selected_private_sessions'] == [99821, 32584] and stage['incoming_prerequisite_session'] == 69321
assert (stage['source_files'], stage['audit_imports'], stage['audit_reports'], stage['independent_reports']) == (6284, 5284, 738, 333)
assert (stage['fresh_reports'], stage['inherited_reports'], stage['combined_reports']) == (3, 529, 532)
assert stage['new_public_theorems'] == stage['new_private_helpers_transitive'] == 3
assert stage['new_definitions'] == stage['new_Prop_definitions'] == stage['definition_checks'] == stage['explicit_private_reports'] == 0
assert stage['resource_reports_inherited'] == 264 and stage['extra_fresh_incoming_recheck_credit'] == 0
push = json.loads((ROOT/stage['prior_checkpoint_push_receipt']).read_text())
assert push['source_commit'] == stage['source_baseline'] == '04e2eb843816747cab7ec59a150d0897619274b4'
assert push['checkpoint_commit'] == push['remote_commit'] == stage['prior_checkpoint'] == PARENT
assert push['actual_push_terminal'] and push['actual_remote_check_terminal']
assert push['actual_push_terminal_exit'] == push['actual_remote_check_terminal_exit'] == push['postpush_current_tree_verifier_terminal_exit'] == 0
overrides = stage['baseline_overrides']
baseline = json.loads(verify(ROOT/stage['source_baseline_path'], stage['source_baseline_sha256']))
assert len(baseline['sources']) == 6283 and len(baseline['toolchain']) == 4
assert len(set(baseline['sources'])-set(OLD_FILES)) == stage['old_other_Source_files_byte_exact'] == 6281
assert {str(p.relative_to(ROOT)) for p in (ROOT/'lean/MicroCFTA').glob('*.lean')} == set(baseline['sources']) | {NEW_FILE}
for name, record in {**baseline['sources'], **baseline['toolchain']}.items():
    verify(ROOT/overrides.get(name, name), record)
normal_pins = json.loads((WORK/'NORMAL-SOURCE-PINS.json').read_text())
assert len(normal_pins) == 6288 and SHA((WORK/'NORMAL-SOURCE-PINS.json').read_bytes()) == stage['normal_source_pins_sha256']
for name, digest in normal_pins.items():
    verify(ROOT/name, digest)

# The incoming-only pass is a prerequisite, not an additional fresh public law.
assert sum(c['fresh_public_reports'] for c in stage['private_subsets']) == 3
assert stage['prerequisite_checks'][0]['fresh_public_reports'] == 0
for check in stage['private_subsets'] + stage['prerequisite_checks']:
    receipt = json.loads((ROOT/check['verified_receipt']).read_text())
    actual = json.loads((ROOT/check['actual_receipt']).read_text())
    runtime = BASE/check['runtime']
    checked = json.loads((runtime/'checked.json').read_text())
    assert receipt['actual_session'] == actual['actual_session'] == check['actual_session']
    assert receipt['actual_terminal'] and actual['actual_terminal']
    assert receipt['actual_terminal_exit'] == actual['actual_terminal_exit'] == 0
    assert receipt['checks'] == checked['checks'] and checked == json.loads((runtime/'results.json').read_text())
    assert receipt['proof_credit'] and receipt['source_pins_unchanged'] and all(checked['passed'])
    assert sum(c['total_axiom_reports'] for c in checked['checks']) == check['expected_reports']
    assert all(c['exit'] == 0 and not c['diagnostics'] and not c['sorryAx'] and not c['nonstandard_axioms']
        and c['declaration_checks'] == 0 for c in checked['checks'])
    assert SHA((runtime/'checked.json').read_bytes()) == receipt['checked_sha256']
    assert SHA((runtime/'source-pins.json').read_bytes()) == receipt['source_pins_sha256']
    pins = json.loads((runtime/'source-pins.json').read_text())
    assert len(pins) == receipt['pins_independently_reverified'] == check['pins']
    for name, digest in pins.items():
        verify(ROOT/overrides.get(name, name), digest)
    if check['name'] == 'incomingPrerequisite':
        assert receipt['executed_control'] == actual['executed_control'] == check['control']
        assert receipt['executed_control_manifest_sha256'] == actual['executed_control_manifest_sha256'] == check['control_manifest_sha256']
for failed in stage['rejected_checks']:
    receipt = json.loads((ROOT/failed['receipt']).read_text())
    runtime = BASE/failed['runtime']
    result = json.loads((runtime/'results.json').read_text())
    assert receipt['actual_session'] == failed['actual_session'] and receipt['actual_terminal'] and receipt['actual_terminal_exit'] == 1
    assert receipt['checks'] == result['checks'] and receipt['credited_public_reports'] == result['credited_public_reports'] == 0
    assert not result['proof_credit'] and not (runtime/'checked.json').exists()
    assert sum(c['diagnostics'] for c in result['checks']) == failed['diagnostics']
    assert any(c['sorryAx'] for c in result['checks']) == failed['sorryAx']
    pins = json.loads((runtime/'source-pins.json').read_text())
    assert len(pins) == receipt['pins_independently_reverified'] == failed['pins']
    for name, digest in pins.items():
        verify(ROOT/overrides.get(name, name), digest)
preflight = json.loads((ROOT/stage['rejected_preparer_receipt']).read_text())
assert preflight['original_control_manifest_sha256'] == '6b65d8fca7328ccf7e07b5ed15937bdccdd118560791a93632659f118b78263e'
assert preflight['actual_terminal_exit'] == 1 and not preflight['compiler_started'] and not preflight['runtime_or_tmp_created']
assert preflight['proof_credit'] == 0

# Bind FINAL actual publication data before freezing this controller. No late supplement.
actual = json.loads((WORK/'PUBLICATION-ACTUAL-RUN.json').read_text())
verified = json.loads((WORK/'PUBLICATION-VERIFIED.json').read_text())
assert actual['actual_terminal'] and verified['actual_terminal']
assert actual['actual_terminal_exit'] == verified['actual_terminal_exit'] == 0
assert type(verified['actual_session']) is int and verified['actual_session'] > 0
assert verified['actual_session'] == actual['actual_session']
assert verified['runtime'] == actual['runtime'] == '20261118-terminal-and-query-seeds-publication'
publication = BASE/verified['runtime']
published = json.loads((publication/'checked.json').read_text())
assert published == json.loads((publication/'results.json').read_text())
assert verified['checks'] == published['checks']
assert SHA((publication/'checked.json').read_bytes()) == verified['checked_sha256']
assert SHA((publication/'source-pins.json').read_bytes()) == verified['source_pins_sha256']
checks = published['checks']
assert [c['name'] for c in checks] == ['public-build', 'strict-new-components-and-prior-bindings', 'independent-imports', 'audit-build', 'audit-strict']
assert [c['total_axiom_reports'] for c in checks] == [738, 3, 333, 738, 738]
assert all(c['exit'] == 0 and not c['diagnostics'] and not c['sorryAx'] and not c['nonstandard_axioms']
    and c['declaration_checks'] == 0 for c in checks)
assert published['all_five_gates_passed'] and published['source_pins_unchanged']
assert (published['source_files'], published['direct_audit_imports'], published['individual_reports'], published['independent_reports']) == (6284, 5284, 738, 333)
assert (published['fresh_reports'], published['inherited_reports'], published['combined_reports']) == (3, 529, 532)
assert published['new_public_theorems'] == published['new_private_theorems'] == 3
assert published['new_theorem_declarations'] == 6 and published['new_prop_definitions'] == 0
assert published['resource_owner_reports_inherited'] == 264 and published['fresh_credit_for_old_owner_theorems'] == 0
assert not published['all_original_eager_worker_query_admissions_proved']
assert not published['native_inhabitance_proved'] and not published['guard_truth_proved']
assert not published['joint_finite_completion_proved'] and not published['haskell_changed']
assert type(published['audited_theorems']) is int and published['audited_theorems'] > 0
assert published['audited_theorems'] == verified['audited_theorems']
pub_pins = json.loads((publication/'source-pins.json').read_text())
assert len(pub_pins) == verified['pins_independently_reverified']
for name, digest in pub_pins.items():
    verify(ROOT/name, digest)

term, seeds = stage['components']
for component in stage['components']:
    packet = BASE/component['packet']
    verify(packet/'MANIFEST.json', component['manifest_sha256'])
    for name, record in records(json.loads((packet/'MANIFEST.json').read_text())):
        verify(packet/name, record)
    current = verify(ROOT/component['source_path'], {'sha256': component['raw_sha256'], 'bytes': component['raw_bytes']})
    assert current == (packet/component['source']).read_bytes()
    for header in component['all_headers']:
        data = verify(ROOT/header['file'], header['sha256']).rstrip()
        assert current.count(data) == 1
        start = current.index(data)
        assert re.match(rb'\s*:= by', current[start+len(data):])
before_term = verify(ROOT/term['old_snapshot'], {'sha256': term['owner_sha256'], 'bytes': 19079})
assert (ROOT/term['source_path']).read_bytes()[208:208+19079] == before_term
base_packet = BASE/seeds['base_packet']
verify(base_packet/'MANIFEST.json', seeds['base_manifest_sha256'])
incoming = verify(base_packet/seeds['base_source'], seeds['base_raw_sha256'])
assert len(incoming) == 17283 and (ROOT/NEW_FILE).read_bytes()[75:75+17283] == incoming
seed_packet = BASE/seeds['packet']
assert (ROOT/NEW_FILE).read_bytes() == (seed_packet/'IMPORTS.lean.txt').read_bytes() + incoming + (seed_packet/'APPEND.lean.txt').read_bytes()
assert len((seed_packet/'APPEND.lean.txt').read_bytes()) == 13793
old_audit = verify(ROOT/overrides['lean/MicroCFTA/Audit.lean'], {'sha256': stage['old_audit_sha256'], 'bytes': 435489})
imports = (WORK/'IMPORTS.lean.txt').read_bytes()
probes = (WORK/'PUBLIC-PROBES.lean.txt').read_bytes()
audit = verify(ROOT/'lean/MicroCFTA/Audit.lean', {'sha256': stage['staged_audit_sha256'], 'bytes': 435886})
assert len(imports) == 66 and imports == b'import MicroCFTA.SourcePruningEnumerationSharedIncomingQuerySeeds\n'
assert audit == imports + old_audit + b'\n' + probes
assert probes == b''.join((BASE/c['packet']/c['probe']).read_bytes() for c in stage['components'])
assert len(re.findall(rb'^#print axioms ', probes, re.M)) == 3
assert len(re.findall(rb'^import ', audit, re.M)) == 5284 and len(re.findall(rb'^#print axioms ', audit, re.M)) == 738
assert all(not (ROOT/name).is_symlink() for name in FILES)
assert GIT('branch', '--show-current').decode().strip() == 'formalize'
assert GIT('rev-parse', 'HEAD').decode().strip() == PARENT
assert not GIT('diff', '--cached', '--name-only')
assert set(GIT('diff', '--name-only', 'HEAD').decode().splitlines()) == set(OLD_FILES)
assert set(GIT('ls-files', '--', *OLD_FILES).decode().splitlines()) == set(OLD_FILES)
assert not GIT('ls-files', '--', NEW_FILE)
assert GIT('show', PARENT+':'+OLD_FILES[0]) == before_term
assert GIT('show', PARENT+':'+OLD_FILES[1]) == old_audit
source_bytes = {name: (ROOT/name).read_bytes() for name in FILES}

# Root executes only this three-file Source commit. No push is performed.
subprocess.run(['git', 'add', '--', *OLD_FILES], check=True, cwd=ROOT)
subprocess.run(['git', 'add', '-f', '--', NEW_FILE], check=True, cwd=ROOT)
assert set(GIT('diff', '--cached', '--name-only').decode().splitlines()) == set(FILES)
for name, data in source_bytes.items():
    assert GIT('show', ':'+name) == data, name
subprocess.run(['git', 'diff', '--cached', '--check'], check=True, cwd=ROOT)
subprocess.run(['git', 'commit', '--quiet', '-m', MESSAGE], check=True, cwd=ROOT)
head = GIT('rev-parse', 'HEAD').decode().strip()
assert GIT('rev-parse', head+'^').decode().strip() == PARENT
assert set(GIT('diff-tree', '--no-commit-id', '--name-only', '-r', head).decode().splitlines()) == set(FILES)
assert not GIT('status', '--porcelain', '--untracked-files=no')
for name, digest in normal_pins.items():
    verify(ROOT/name, digest)
receipt = {'at': datetime.datetime.now().astimezone().isoformat(), 'source_commit': head,
    'parent': PARENT, 'files': FILES, 'actual_terminal': True, 'actual_terminal_exit': 0,
    'message': MESSAGE, 'private_actual_sessions': [99821, 69321, 32584],
    'selected_private_sessions': [99821, 32584], 'incoming_prerequisite_extra_credit': 0,
    'rejected_sessions': [23666, 54752], 'rejected_proof_credit': 0,
    'publication_actual_session': verified['actual_session'], 'audited_theorems': published['audited_theorems'],
    'publication_pins_independently_reverified': verified['pins_independently_reverified'],
    'source_files': 6284, 'audit_imports': 5284, 'audit_reports': 738, 'independent_reports': 333,
    'fresh_public_reports': 3, 'inherited_reports': 529, 'combined_reports': 532,
    'new_public_theorems': 3, 'new_private_theorems': 3, 'new_definitions': 0,
    'resource_reports_inherited': 264, 'old_terminal_bytes': 19079, 'old_terminal_offset': 208,
    'incoming_prefix_bytes': 17283, 'incoming_prefix_offset': 75,
    'old_audit_bytes': 435489, 'old_audit_offset': 66, 'all_FIRST_headers_checked_by_full_body': True,
    'future_raw_cached_semantic_packets_included': False,
    'all_original_eager_worker_query_admissions_proved': False,
    'native_inhabitance_proved': False, 'guard_truth_proved': False,
    'joint_finite_completion_proved': False, 'haskell_changed': False}
(WORK/'SOURCE-COMMIT.json').write_text(json.dumps(receipt, indent=2)+'\n')
print(json.dumps(receipt))
