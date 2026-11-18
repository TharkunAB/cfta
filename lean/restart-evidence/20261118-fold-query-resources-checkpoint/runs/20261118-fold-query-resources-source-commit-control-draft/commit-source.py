from pathlib import Path
import datetime
import hashlib
import json
import re
import subprocess

ROOT = Path('/home/tritlo/Code/mcfta')
BASE = ROOT / 'lean/restart-evidence'
CONTROL = BASE / '20261118-fold-query-resources-source-commit-control-draft'
WORK = BASE / '20261118-ordered-fold-query-resources-work'
PARENT = '6546febba4473d4347d8e4d4c68ea1c90cb7dae3'
MESSAGE = 'Preserve query resources through raw and cached folds'
FILES = ['lean/MicroCFTA/SourcePruningEnumerationSharedTerminalFoldQueryEvents.lean',
    'lean/MicroCFTA/Audit.lean']
assert Path(__file__).resolve().parent == WORK.resolve(), 'Root reviews and copies this exact controller.'
assert Path(__file__).read_bytes() == (CONTROL / 'commit-source.py').read_bytes()
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


for name, record in records(json.loads((CONTROL / 'MANIFEST.json').read_text())):
    verify(CONTROL / name, record)
for name, record in json.loads((CONTROL / 'SOURCE-PINS.json').read_text()).items():
    verify(ROOT / name, record)
assert not (WORK / 'SOURCE-COMMIT.json').exists(), 'Preserve any existing commit receipt.'
stage = json.loads((WORK / 'SOURCES-NORMAL-STAGING.json').read_text())
assert stage['status'] == 'SOURCE_NORMAL_STAGING_COMPLETED' and stage['normal_Source_changed']
assert stage['actual_private_session'] == 70278 and stage['raw_private_session'] == 49861
assert stage['first_failed_session'] == 19321
assert len(stage['components']) == 1
assert set(stage['exact_Source_write_paths']) == set(stage['baseline_overrides']) == set(FILES)
assert (stage['source_files'], stage['audit_imports'], stage['audit_reports'], stage['independent_reports']) == (6283, 5283, 735, 330)
assert (stage['fresh_reports'], stage['inherited_reports'], stage['combined_reports']) == (2, 527, 529)
assert stage['new_public_theorems'] == 2 and stage['new_private_helpers_transitive'] == 0
assert stage['new_modules'] == stage['new_definitions'] == stage['new_Prop_definitions'] == 0
assert stage['definition_checks'] == stage['explicit_private_reports'] == 0
assert stage['resource_reports_inherited'] == 264 and stage['fresh_credit_for_old_owner_theorems'] == 0
assert stage['publication_component_credit'] == {'RawFold': 1, 'CachedFold': 1, 'total': 2,
    'RawFold_recheck_not_added_again': True}
push = json.loads((ROOT / stage['prior_checkpoint_push_receipt']).read_text())
assert push['checkpoint_commit'] == push['remote_commit'] == PARENT
assert push['source_commit'] == stage['source_baseline'] == 'f8feb9f2dc42b8213c002281cdbce449404ab2f9'
assert push['actual_push_terminal'] and push['actual_remote_check_terminal']
assert push['actual_push_terminal_exit'] == push['actual_remote_check_terminal_exit'] == 0
assert push['postpush_current_tree_verifier_terminal_exit'] == 0 and push['normal_Source_files'] == 6283
overrides = stage['baseline_overrides']
baseline = json.loads(verify(ROOT / stage['source_baseline_path'], stage['source_baseline_sha256']))
assert len(baseline['sources']) == 6283 and len(baseline['toolchain']) == 4
assert len(set(baseline['sources']) - set(FILES)) == stage['old_other_Source_files_byte_exact'] == 6281
assert {str(p.relative_to(ROOT)) for p in (ROOT / 'lean/MicroCFTA').glob('*.lean')} == set(baseline['sources'])
for name, record in {**baseline['sources'], **baseline['toolchain']}.items():
    verify(ROOT / overrides.get(name, name), record)
normal_pins = json.loads((WORK / 'NORMAL-SOURCE-PINS.json').read_text())
assert SHA((WORK / 'NORMAL-SOURCE-PINS.json').read_bytes()) == stage['normal_source_pins_sha256']
assert len(normal_pins) == 6287
for name, digest in normal_pins.items():
    verify(ROOT / name, digest)

# Keep the rejected first check separate from the two passed private checks.
first = json.loads((WORK / 'FIRST-CHECK-REJECTED.json').read_text())
first_runtime = BASE / first['runtime']
assert first['actual_session'] == 19321 and first['actual_terminal'] and first['actual_terminal_exit'] == 1
assert first['credited_public_reports'] == 0 and not (first_runtime / 'checked.json').exists()
assert first['checks'] == json.loads((first_runtime / 'results.json').read_text())['checks']
assert first['checks'][0]['diagnostics'] == first['checks'][0]['exit'] == 1
assert not first['checks'][0]['sorryAx'] and not first['checks'][0]['nonstandard_axioms']
assert SHA((first_runtime / 'results.json').read_bytes()) == first['results_sha256']
for receipt_name, session, reports, count in [('REPAIR-CHECK-VERIFIED.json', 49861, 1, 8283),
    ('CACHED-CHECK-VERIFIED.json', 70278, 2, 8330)]:
    private = json.loads((WORK / receipt_name).read_text())
    private_runtime = BASE / private['runtime']
    checked = json.loads((private_runtime / 'checked.json').read_text())
    assert private['actual_session'] == session and private['actual_terminal'] and private['actual_terminal_exit'] == 0
    assert private['checks'] == checked['checks'] and checked == json.loads((private_runtime / 'results.json').read_text())
    assert private['proof_credit'] and private['source_pins_unchanged'] and all(checked['passed'])
    assert sum(c['total_axiom_reports'] for c in checked['checks']) == reports
    assert all(c['exit'] == 0 and not c['diagnostics'] and not c['sorryAx'] and not c['nonstandard_axioms']
        and c['declaration_checks'] == 0 for c in checked['checks'])
    assert SHA((private_runtime / 'checked.json').read_bytes()) == private['checked_sha256']
    assert SHA((private_runtime / 'source-pins.json').read_bytes()) == private['source_pins_sha256']
    pins = json.loads((private_runtime / 'source-pins.json').read_text())
    assert len(pins) == private['pins_independently_reverified'] == count
    for name, digest in pins.items():
        verify(ROOT / overrides.get(name, name), digest)
first_pins = json.loads((first_runtime / 'source-pins.json').read_text())
assert len(first_pins) == first['pins_independently_reverified'] == 6332
assert SHA((first_runtime / 'source-pins.json').read_bytes()) == first['source_pins_sha256']
for name, digest in first_pins.items():
    verify(ROOT / overrides.get(name, name), digest)

# These FINAL receipts and their exact byte hashes are bound before this controller freezes.
actual = json.loads((WORK / 'PUBLICATION-ACTUAL-RUN.json').read_text())
verified = json.loads((WORK / 'PUBLICATION-VERIFIED.json').read_text())
assert actual['actual_terminal'] and verified['actual_terminal']
assert actual['actual_terminal_exit'] == verified['actual_terminal_exit'] == 0
assert type(verified['actual_session']) is int and verified['actual_session'] > 0
assert verified['actual_session'] == actual['actual_session']
assert verified['runtime'] == actual['runtime'] == '20261118-fold-query-resources-publication'
publication = BASE / verified['runtime']
published = json.loads((publication / 'checked.json').read_text())
assert published == json.loads((publication / 'results.json').read_text())
assert verified['checks'] == published['checks']
assert SHA((publication / 'checked.json').read_bytes()) == verified['checked_sha256']
assert SHA((publication / 'source-pins.json').read_bytes()) == verified['source_pins_sha256']
checks = published['checks']
assert [c['name'] for c in checks] == ['public-build', 'strict-new-components-and-prior-bindings',
    'independent-imports', 'audit-build', 'audit-strict']
assert [c['total_axiom_reports'] for c in checks] == [735, 2, 330, 735, 735]
assert all(c['exit'] == 0 and not c['diagnostics'] and not c['sorryAx'] and not c['nonstandard_axioms']
    and c['declaration_checks'] == 0 for c in checks)
assert published['all_five_gates_passed'] and published['source_pins_unchanged']
assert (published['source_files'], published['direct_audit_imports'], published['individual_reports'], published['independent_reports']) == (6283, 5283, 735, 330)
assert (published['fresh_reports'], published['inherited_reports'], published['combined_reports']) == (2, 527, 529)
assert published['new_public_theorems'] == published['new_theorem_declarations'] == 2
assert published['new_private_theorems'] == published['new_prop_definitions'] == 0
assert published['resource_owner_reports_inherited'] == 264 and published['fresh_credit_for_old_owner_theorems'] == 0
assert published['actual_raw_private_session'] == 49861 and published['actual_combined_private_session'] == 70278
assert published['failed_first_attempt'] == 19321 and published['failed_first_attempt_proof_credit'] == 0
assert published['both_original_FIRST_headers_exact'] and published['all_old_proof_bodies_and_limits_unchanged']
assert published['actual_ordered_rawFold_query_event_resources_checked'] and published['actual_cached_fold_query_event_resources_checked']
assert published['all_original_supplied_fuels_and_endpoints_retained']
assert not published['all_original_eager_worker_query_admissions_proved']
assert not published['native_inhabitance_proved'] and not published['guard_truth_proved']
assert not published['joint_finite_completion_proved'] and not published['haskell_changed']
assert type(published['audited_theorems']) is int and published['audited_theorems'] > 0
assert published['audited_theorems'] == verified['audited_theorems']
pub_pins = json.loads((publication / 'source-pins.json').read_text())
assert len(pub_pins) == verified['pins_independently_reverified']
for name, digest in pub_pins.items():
    verify(ROOT / name, digest)

item = stage['components'][0]
packet = BASE / item['packet']
verify(packet / 'MANIFEST.json', item['manifest_sha256'])
for name, record in records(json.loads((packet / 'MANIFEST.json').read_text())):
    verify(packet / name, record)
current = verify(ROOT / item['source_path'], {'sha256': item['raw_sha256'], 'bytes': item['raw_bytes']})
assert current == (packet / item['source']).read_bytes()
before = verify(ROOT / item['old_snapshot'], {'sha256': item['owner_sha256'], 'bytes': 15875})
raw_packet = BASE / item['raw_base_packet']
verify(raw_packet / 'MANIFEST.json', item['raw_base_manifest_sha256'])
raw_base = verify(raw_packet / item['raw_base_source'], item['raw_base_sha256'])
assert len(raw_base) == 25278 and current == raw_base + (packet / item['append']).read_bytes()
assert current[136:136 + 15875] == before
for header in item['all_public_headers']:
    data = verify(ROOT / header['file'], header['sha256'])
    start = current.index(data.splitlines()[0])
    assert current[start:current.index(b':= by', start)].rstrip() == data.rstrip()
probes = verify(packet / item['probe'], item['probe_sha256'])
assert re.findall(r'^#print axioms (\S+)', probes.decode(), re.M) == item['public_qnames']
assert len(item['public_qnames']) == 2 and b'#check ' not in probes
old_audit = verify(ROOT / overrides['lean/MicroCFTA/Audit.lean'],
    {'sha256': stage['old_audit_sha256'], 'bytes': 435271})
audit = verify(ROOT / 'lean/MicroCFTA/Audit.lean', {'sha256': stage['staged_audit_sha256'], 'bytes': 435489})
assert audit == old_audit + b'\n' + probes
assert len(re.findall(rb'^import ', old_audit, re.M)) == len(re.findall(rb'^import ', audit, re.M)) == 5283
assert len(re.findall(rb'^#print axioms ', old_audit, re.M)) == 733
assert len(re.findall(rb'^#print axioms ', audit, re.M)) == 735
assert all(not (ROOT / name).is_symlink() for name in FILES)
assert GIT('branch', '--show-current').decode().strip() == 'formalize'
assert GIT('rev-parse', 'HEAD').decode().strip() == PARENT
assert not GIT('diff', '--cached', '--name-only')
assert set(GIT('diff', '--name-only', 'HEAD').decode().splitlines()) == set(FILES)
assert set(GIT('ls-files', '--', *FILES).decode().splitlines()) == set(FILES)
assert GIT('show', PARENT + ':' + FILES[0]) == before
assert GIT('show', PARENT + ':' + FILES[1]) == old_audit
source_bytes = {name: (ROOT / name).read_bytes() for name in FILES}

# Root approves and executes this exact two-file Source commit. No push is performed.
subprocess.run(['git', 'add', '--', *FILES], check=True, cwd=ROOT)
assert set(GIT('diff', '--cached', '--name-only').decode().splitlines()) == set(FILES)
for name, data in source_bytes.items():
    assert GIT('show', ':' + name) == data, name
subprocess.run(['git', 'diff', '--cached', '--check'], check=True, cwd=ROOT)
subprocess.run(['git', 'commit', '--quiet', '-m', MESSAGE], check=True, cwd=ROOT)
head = GIT('rev-parse', 'HEAD').decode().strip()
assert GIT('rev-parse', head + '^').decode().strip() == PARENT
assert set(GIT('diff-tree', '--no-commit-id', '--name-only', '-r', head).decode().splitlines()) == set(FILES)
assert not GIT('status', '--porcelain', '--untracked-files=no')
for name, digest in normal_pins.items():
    verify(ROOT / name, digest)
receipt = {'at': datetime.datetime.now().astimezone().isoformat(), 'source_commit': head,
    'parent': PARENT, 'files': FILES, 'actual_terminal': True, 'actual_terminal_exit': 0,
    'message': MESSAGE, 'private_actual_sessions': [49861, 70278], 'first_failed_session': 19321,
    'first_failed_credit': 0, 'publication_actual_session': verified['actual_session'],
    'audited_theorems': published['audited_theorems'],
    'publication_pins_independently_reverified': verified['pins_independently_reverified'],
    'source_files': 6283, 'audit_imports': 5283, 'audit_reports': 735,
    'independent_reports': 330, 'fresh_public_reports': 2, 'inherited_reports': 527,
    'combined_reports': 529, 'new_public_theorems': 2, 'new_private_theorems': 0,
    'new_definitions': 0, 'resource_reports_inherited': 264,
    'old_fold_owner_bytes': 15875, 'old_fold_owner_offset': 136,
    'whole_checked_RawFold_prefix_bytes': 25278,
    'old_audit_contiguous_bytes': 435271, 'old_audit_offset': 0,
    'both_original_FIRST_headers_checked': True,
    'all_original_eager_worker_query_admissions_proved': False,
    'native_inhabitance_proved': False, 'guard_truth_proved': False,
    'joint_finite_completion_proved': False, 'haskell_changed': False}
(WORK / 'SOURCE-COMMIT.json').write_text(json.dumps(receipt, indent=2) + '\n')
print(json.dumps(receipt))
