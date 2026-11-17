from pathlib import Path
import datetime
import hashlib
import json
import re
import subprocess

root = Path('/home/tritlo/Code/mcfta')
base = root / 'lean/restart-evidence'
control = base / '20261117-numerical-seed-closure-source-commit-control-draft'
expected = json.loads((control / 'EXPECTED-COMMIT.json').read_text())
work = base / expected['work']
assert Path(__file__).resolve().parent == work.resolve(), 'Root must review and copy this controller.'
assert Path(__file__).read_bytes() == (control / 'commit-source.py').read_bytes()
sha = lambda data: hashlib.sha256(data).hexdigest()
git = lambda *args: subprocess.check_output(['git', *args], cwd=root)
files = expected['files']
new_sources = set(expected['new_force_added_source_files'])
tracked_sources = set(expected['tracked_source_changes'])
assert len(files) == len(set(files)) == 14
assert len(new_sources) == 8 and len(tracked_sources) == 6
assert set(files) == new_sources | tracked_sources
assert all(name.startswith('lean/MicroCFTA/') and name.endswith('.lean') for name in files)


def verify(path, record):
    data = path.read_bytes()
    digest = record['sha256'] if isinstance(record, dict) else record
    assert sha(data) == digest, str(path)
    if isinstance(record, dict) and 'bytes' in record:
        assert len(data) == record['bytes'], str(path)
    return data


for name, record in json.loads((control / 'MANIFEST.json').read_text())['files'].items():
    verify(control / name, record)
for name, record in json.loads((control / 'SOURCE-PINS.json').read_text()).items():
    verify(root / name, record)
assert not (work / 'SOURCE-COMMIT.json').exists()
stage = json.loads((work / 'SOURCES-NORMAL-STAGING.json').read_text())
assert stage['status'] == 'ACTUALLY STAGED BY ROOT AFTER VERIFIED TERMINAL PASS'
assert stage['prior_checkpoint'] == expected['parent']
assert stage['source_baseline'] == expected['source_baseline']
assert len(stage['components']) == 13 and stage['source_files'] == 6278
assert stage['audit_imports'] == 5278 and stage['fresh_public_reports'] == 15
assert stage['audit_reports'] == 724 and stage['owning_private_reports_not_in_audit'] == 2
assert {item['source_path'] for item in stage['components']} | {'lean/MicroCFTA/Audit.lean'} == set(files)
assert {item['source_path'] for item in stage['components'] if item['kind'] == 'new_module'} == new_sources
assert set(stage['baseline_overrides']) == tracked_sources
assert not stage['joint_finite_completion_proved'] and not stage['haskell_changed']

prior_push = json.loads((base / '20261117-third-query-node-seed-work/PUSH-VERIFIED.json').read_text())
assert prior_push['source_commit'] == expected['source_baseline']
assert prior_push['checkpoint_commit'] == prior_push['remote_commit'] == expected['parent']
assert prior_push['actual_push_terminal'] and prior_push['actual_push_terminal_exit'] == 0
assert prior_push['actual_remote_check_terminal'] and prior_push['actual_remote_check_terminal_exit'] == 0
assert prior_push['postpush_current_tree_verifier_terminal_exit'] == 0
private = base / stage['runtime']
private_receipt = json.loads((work / 'SEED-CLOSURE-VERIFIED.json').read_text())
private_checked = json.loads(verify(private / 'checked.json', private_receipt['checked_sha256']))
assert private_receipt['actual_terminal'] and private_receipt['actual_terminal_exit'] == 0
assert type(private_receipt['actual_session']) is int and private_receipt['actual_session'] > 0
assert private_receipt['actual_session'] == stage['actual_private_session']
assert private_receipt['checks'] == private_checked['checks']
assert private_receipt['all_thirteen_components_checked'] and all(private_checked['passed'])
assert private_receipt['actual_public_reports'] == 15 and private_receipt['actual_owning_private_reports'] == 2
assert private_receipt['actual_total_reports'] == 17 and private_receipt['actual_definition_checks'] == 1
assert private_receipt['Prop_axiom_credit'] == 0
private_pin_bytes = verify(private / 'source-pins.json', private_receipt['source_pins_sha256'])
private_pins = json.loads(private_pin_bytes)
assert private_receipt['pins_independently_reverified'] == len(private_pins)
for name, digest in private_pins.items():
    verify(root / stage['baseline_overrides'].get(name, name), digest)

# Root creates this final receipt only after all actual public gates terminate.
publication_control = base / expected['publication_control']
verify(publication_control / 'MANIFEST.json', expected['publication_control_sha256'])
publication = base / expected['publication_runtime']
verified = json.loads((work / expected['future_publication_receipt']).read_text())
assert type(verified['actual_session']) is int and verified['actual_session'] > 0
assert verified['actual_terminal'] and verified['actual_terminal_exit'] == 0
assert verified['runtime'] == publication.name
published = json.loads(verify(publication / 'checked.json', verified['checked_sha256']))
assert json.loads((publication / 'results.json').read_text()) == published
assert published['checks'] == verified['checks'] == json.loads((publication / 'checks.json').read_text())
checks = published['checks']
assert len(checks) == 5
assert [item['name'] for item in checks] == [
    'public-build', 'strict-new-components-and-prior-bindings', 'independent-imports',
    'audit-build', 'audit-strict']
assert [item['total_axiom_reports'] for item in checks] == expected['expected_five_report_counts']
assert [item['declaration_checks'] for item in checks] == expected['expected_five_declaration_counts']
assert all(item['exit'] == 0 and not item['diagnostics'] and not item['sorryAx']
    and not item['nonstandard_axioms'] for item in checks)
assert checks[1]['axiom_groups'] == 15 and checks[1]['axiom_free_reports'] == 0
assert checks[2]['axiom_groups'] == 316 and checks[2]['axiom_free_reports'] == 3
assert checks[4]['axiom_groups'] == 718 and checks[4]['axiom_free_reports'] == 6
assert published['all_five_gates_passed'] and published['source_pins_unchanged']
assert published['source_files'] == verified['source_files'] == 6278
assert published['direct_audit_imports'] == verified['direct_audit_imports'] == 5278
assert published['independent_reports'] == verified['independent_reports'] == 319
assert verified['definition_checks'] == 1 and verified['Prop_axiom_credit'] == 0
assert published['new_definition_declaration_checks'] == 1 and published['new_definition_axiom_credit'] == 0
assert published['fresh_strict_normal_reports'] == 15 and published['new_public_theorems'] == 15
assert published['private_owning_module_reports_bound_separately'] == 2
assert published['actual_admitted_query_sequence_Seeds_producer_checked']
assert not published['all_original_eager_worker_query_admissions_proved']
assert not published['original_eager_worker_all_calls_Seeds_propagation_proved']
assert not published['native_inhabitance_proved'] and not published['joint_finite_completion_proved']
assert not published['haskell_changed']
assert type(published['audited_theorems']) is int and published['audited_theorems'] > 0
assert published['audited_theorems'] == verified['audited_theorems']
pub_pin_bytes = verify(publication / 'source-pins.json', verified['source_pins_sha256'])
pub_pins = json.loads(pub_pin_bytes)
assert verified['pins_independently_reverified'] == len(pub_pins)
for name, digest in pub_pins.items():
    verify(root / name, digest)
source_paths = {str(path.relative_to(root)) for path in (root / 'lean/MicroCFTA').glob('*.lean')}
assert len(source_paths) == 6278 and source_paths <= set(pub_pins)

# Recheck the exact selected headers and every complete old owner block.
public_names = []
for item in stage['components']:
    packet = base / item['packet']
    current = verify(root / item['source_path'], {'sha256': item['raw_sha256'], 'bytes': item['raw_bytes']})
    if item['kind'] == 'existing_owner_EOF':
        before = verify(root / item['old_snapshot'],
            {'sha256': item['owner_sha256'], 'bytes': item['owner_bytes']})
        imported = verify(packet / item['import_prefix'], item['import_prefix_sha256']) if item.get('import_prefix') else b''
        appended = verify(packet / item['append'], item['append_sha256'])
        assert current == imported + before + appended
        assert item['old_owner_offset'] == len(imported)
        assert current[len(imported):len(imported) + len(before)] == before
        if item['raw_stored_in_packet']:
            assert current == (packet / item['source']).read_bytes()
    else:
        assert item['kind'] == 'new_module' and current == (packet / item['source']).read_bytes()
    for header in item['headers']:
        data = verify(packet / header['file'], header['sha256'])
        assert data.rstrip(b'\n') in current
    public_names.extend(item['public_qnames'])
assert len(public_names) == len(set(public_names)) == 15
old_audit = verify(work / 'SEED-CLOSURE-Audit-BEFORE.lean.txt',
    {'sha256': stage['old_audit_sha256'], 'bytes': stage['old_audit_bytes']})
imports = (work / 'IMPORTS.lean.txt').read_bytes()
public_probes = (work / 'PUBLIC-PROBES.lean.txt').read_bytes()
assert public_probes == ''.join('#print axioms ' + name + '\n' for name in public_names).encode()
assert len(re.findall(rb'^import ', imports, re.M)) == 8
assert public_probes.count(b'#print axioms ') == 15 and b'#check ' not in public_probes
assert b'execute_returned_of_actual_prefixes' not in public_probes
assert b'seeds_preserved_at_every_actual_query_endpoint' not in public_probes
assert (root / 'lean/MicroCFTA/Audit.lean').read_bytes() == imports + old_audit + b'\n' + public_probes
baseline = json.loads(verify(root / stage['source_baseline_path'], stage['source_baseline_sha256']))
assert source_paths == set(baseline['sources']) | new_sources
for name, record in baseline['sources'].items():
    if name not in tracked_sources:
        verify(root / name, record)
for name, record in baseline['toolchain'].items():
    verify(root / name, record)
assert len(baseline['sources']) - len(tracked_sources) == 6264

# No Git write occurs until all source bytes and actual receipts above pass.
assert git('branch', '--show-current').decode().strip() == expected['branch'] == 'formalize'
assert git('rev-parse', 'HEAD').decode().strip() == expected['parent']
assert not git('diff', '--cached', '--name-only', '-z')
assert set(filter(None, git('diff', '--name-only', '-z', 'HEAD').decode().split('\0'))) == tracked_sources
for name in new_sources:
    assert not git('ls-files', '--', name), name
source_bytes = {name: (root / name).read_bytes() for name in files}
assert all(not (root / name).is_symlink() for name in files)

# Root alone executes this exact fourteen-file Source commit.
subprocess.run(['git', 'add', '-f', '--', *files], check=True, cwd=root)
assert set(filter(None, git('diff', '--cached', '--name-only', '-z').decode().split('\0'))) == set(files)
for name, data in source_bytes.items():
    assert git('show', ':' + name) == data, name
subprocess.run(['git', 'diff', '--cached', '--check'], check=True, cwd=root)
subprocess.run(['git', 'commit', '--quiet', '-m', expected['message']], check=True, cwd=root)
head = git('rev-parse', 'HEAD').decode().strip()
assert git('rev-parse', head + '^').decode().strip() == expected['parent']
assert set(filter(None, git('diff-tree', '--no-commit-id', '--name-only', '-z', '-r', head).decode().split('\0'))) == set(files)
assert git('log', '-1', '--format=%B').decode().strip() == expected['message']
assert not git('status', '--porcelain', '--untracked-files=no')
receipt = {'at': datetime.datetime.now().astimezone().isoformat(), 'source_commit': head,
    'parent': expected['parent'], 'files': files, 'actual_terminal': True, 'actual_terminal_exit': 0,
    'message': expected['message'], 'private_actual_session': private_receipt['actual_session'],
    'publication_actual_session': verified['actual_session'], 'audited_theorems': published['audited_theorems'],
    'source_files': 6278, 'direct_audit_imports': 5278, 'fresh_public_reports': 15,
    'owning_private_reports_separate': 2, 'Prop_definition_axiom_credit': 0,
    'all_selected_first_headers_preserved': True, 'all_old_Source_owner_blocks_preserved': True,
    'old_other_source_files_byte_exact': 6264,
    'actual_admitted_query_sequence_Seeds_producer_checked': True,
    'all_original_eager_worker_query_admissions_proved': False,
    'native_inhabitance_proved': False, 'joint_finite_completion_proved': False, 'haskell_changed': False}
(work / 'SOURCE-COMMIT.json').write_text(json.dumps(receipt, indent=2) + '\n')
print(json.dumps(receipt))
