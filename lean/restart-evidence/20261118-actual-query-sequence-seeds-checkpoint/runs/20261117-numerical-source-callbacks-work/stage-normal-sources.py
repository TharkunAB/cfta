from pathlib import Path
import datetime
import hashlib
import json
import re

root = Path('/home/tritlo/Code/mcfta')
base = root / 'lean/restart-evidence'
control = base / '20261117-numerical-seed-closure-repair-staging-control-draft'
sha = lambda data: hashlib.sha256(data).hexdigest()
stage = json.loads((control / 'EXPECTED-STAGE.json').read_text())
work = base / stage['work']
assert Path(__file__).resolve().parent == work.resolve(), 'Root must review and copy this controller.'
assert Path(__file__).read_bytes() == (control / 'stage-normal-sources.py').read_bytes()


def verify(path, record):
    data = path.read_bytes()
    digest = record['sha256'] if isinstance(record, dict) else record
    assert sha(data) == digest, str(path)
    if isinstance(record, dict) and 'bytes' in record:
        assert len(data) == record['bytes'], str(path)
    return data


def records(value):
    return list(value.items()) if isinstance(value, dict) else [(item['path'], item) for item in value]


for name, record in json.loads((control / 'MANIFEST.json').read_text())['files'].items():
    verify(control / name, record)
for name, record in json.loads((control / 'CONTROL-AND-PRIOR-RECEIPT-PINS.json').read_text()).items():
    verify(root / name, record)
private_control = base / stage['private_control']
verify(private_control / 'MANIFEST.json', stage['private_control_manifest_sha256'])
selection_bytes = verify(private_control / 'SELECTION.json', stage['private_selection_sha256'])
assert selection_bytes == (control / 'CHECK-SELECTION.json').read_bytes()
selection = json.loads(selection_bytes)
assert len(selection['components']) == selection['expected_checks'] == 13
assert selection['source_commit'] == stage['source_baseline']
assert selection['runtime'] == stage['runtime']
run = base / stage['runtime']
selected = json.loads((run / 'selection.json').read_text())
assert selected['components'] == selection['components']
assert selected['compile_order'] == selection['compile_order']
assert selected['control_manifest_sha256'] == stage['private_control_manifest_sha256']
assert selected['actual_source_commit'] == stage['source_baseline']

# This receipt does not exist at controller freeze. Root supplies actual data.
receipt_path = work / stage['future_verified_receipt']
receipt = json.loads(receipt_path.read_text())
assert type(receipt['actual_session']) is int and receipt['actual_session'] > 0
assert receipt['actual_terminal'] and receipt['actual_terminal_exit'] == 0
assert receipt['runtime'] == stage['runtime']
assert receipt['source_baseline'] == stage['source_baseline'] and receipt['source_files'] == 6270
assert receipt['actual_public_reports'] == 15 and receipt['actual_owning_private_reports'] == 2
assert receipt['actual_total_reports'] == 17 and receipt['actual_definition_checks'] == 1
assert receipt['new_private_helpers_transitive'] == 10 and receipt['new_Prop_definitions'] == 1
assert receipt['Prop_axiom_credit'] == 0
assert receipt['all_thirteen_components_checked']
assert receipt['actual_admitted_query_sequence_Seeds_producer_checked']
assert not receipt['normal_Source_changed'] and not receipt['published']
assert not receipt['original_eager_worker_all_calls_Seeds_propagation_proved']
assert not receipt['joint_finite_completion_proved'] and not receipt['haskell_changed']
checked_bytes = verify(run / 'checked.json', receipt['checked_sha256'])
checked = json.loads(checked_bytes)
assert json.loads((run / 'results.json').read_text()) == checked
assert checked['checks'] == receipt['checks'] == json.loads((run / 'checks.json').read_text())
assert len(checked['checks']) == 13 and len(checked['passed']) == 13 and all(checked['passed'])
assert checked['all_thirteen_seed_closure_components_checked'] and checked['normal_module_checked']
assert checked['failure'] is None and checked['source_pins_unchanged']
assert checked['source_commit'] == stage['source_baseline']
assert not checked['normal_source_changed'] and not checked['published']
assert checked['actual_public_axiom_reports'] == 15
assert checked['actual_owning_private_axiom_reports'] == 2 and checked['actual_total_axiom_reports'] == 17
assert checked['actual_definition_declaration_checks'] == 1
assert checked['new_private_helpers_compiled_transitively'] == 10
assert checked['Prop_definition_axiom_report_credit'] == 0
assert checked['public_actual_finite_query_sequence_Seeds_producer_checked']
assert checked['limits'] == {'memory.max': '8589934592', 'memory.high': '8589934592', 'memory.swap.max': '0'}
component_by_name = {item['module']: item for item in selection['components']}
for result, name in zip(checked['checks'], selection['compile_order']):
    item = component_by_name[name]
    assert result['name'] == name and result['exit'] == 0
    assert not result['diagnostics'] and not result['sorryAx'] and not result['nonstandard_axioms']
    assert result['total_axiom_reports'] == item['expected_axiom_reports']
    assert result['declaration_checks'] == item['expected_declaration_checks']
pin_bytes = verify(run / 'source-pins.json', receipt['source_pins_sha256'])
pins = json.loads(pin_bytes)
assert receipt['pins_independently_reverified'] == len(pins) > 0
for name, digest in pins.items():
    verify(root / name, digest)

# Source55 and its pushed checkpoint are real prior receipts, not future claims.
prior = base / '20261117-third-query-node-seed-work'
source = json.loads((prior / 'SOURCE-COMMIT.json').read_text())
push = json.loads((prior / 'PUSH-VERIFIED.json').read_text())
assert source['actual_terminal'] and source['actual_terminal_exit'] == 0
assert source['source_commit'] == push['source_commit'] == stage['source_baseline']
assert push['checkpoint_commit'] == push['remote_commit'] == stage['prior_checkpoint']
assert push['actual_push_terminal'] and push['actual_push_terminal_exit'] == 0
assert push['actual_remote_check_terminal'] and push['actual_remote_check_terminal_exit'] == 0
assert push['postpush_current_tree_verifier_terminal_exit'] == 0
baseline = json.loads(verify(root / stage['source_baseline_path'], stage['source_baseline_sha256']))
assert baseline['source_commit'] == stage['source_baseline']
sources = sorted((root / 'lean/MicroCFTA').glob('*.lean'))
assert len(sources) == 6270 and {str(path.relative_to(root)) for path in sources} == set(baseline['sources'])
for name, record in {**baseline['sources'], **baseline['toolchain']}.items():
    verify(root / name, record)

old_audit = verify(root / 'lean/MicroCFTA/Audit.lean',
    {'sha256': stage['old_audit_sha256'], 'bytes': stage['old_audit_bytes']})
assert old_audit.count(b'#print axioms ') == 709
assert len(re.findall(rb'^import ', old_audit, re.M)) == 5270
replacements = {}
snapshots = {}
new_names = []
public_names = []
for item, chosen in zip(stage['components'], selection['components']):
    for key, value in chosen.items():
        assert item[key] == value, (item['module'], key)
    packet = base / item['packet']
    manifest = json.loads(verify(packet / 'MANIFEST.json', item['manifest_sha256']))
    for name, record in records(manifest['files']):
        verify(packet / name, record)
    if item['kind'] == 'existing_owner_EOF':
        before = verify(root / item['owner_source'],
            {'sha256': item['owner_sha256'], 'bytes': item['owner_bytes']})
        imported = verify(packet / item['import_prefix'], item['import_prefix_sha256']) if item.get('import_prefix') else b''
        appended = verify(packet / item['append'], item['append_sha256'])
        raw = imported + before + appended
        assert item['old_owner_offset'] == len(imported)
        assert raw[len(imported):len(imported) + len(before)] == before
        if item['raw_stored_in_packet']:
            assert (packet / item['source']).read_bytes() == raw
        snapshots[root / item['old_snapshot']] = before
        declarations = appended
    else:
        assert item['kind'] == 'new_module'
        assert not (root / item['source_path']).exists()
        raw = (packet / item['source']).read_bytes()
        declarations = raw
        new_names.append(item['module'])
    assert len(raw) == item['raw_bytes'] and sha(raw) == item['raw_sha256']
    assert b'#print axioms ' not in raw and b'#check ' not in raw
    assert not re.search(rb'set_option\s+(maxHeartbeats|maxRecDepth|warningAsError|linter\.)', declarations)
    for header in item['headers']:
        text = verify(packet / header['file'], header['sha256'])
        assert text.rstrip(b'\n') in declarations
    probe_records = item.get('probe_files', [{'file': item.get('probe'), 'sha256': item.get('probe_sha256')}])
    probe = b''.join(verify(packet / record['file'], record['sha256']) for record in probe_records)
    if item.get('declaration_probe'):
        probe += b'\n' + verify(packet / item['declaration_probe'], item['declaration_probe_sha256'])
    assert (run / 'source/MicroCFTA' / item['source']).read_bytes() == raw + b'\n' + probe
    replacements[root / item['source_path']] = raw
    public_names.extend(item['public_qnames'])
assert len(new_names) == 8 and len(replacements) == 13
public = ''.join('#print axioms ' + name + '\n' for name in public_names).encode()
assert public == (control / 'PUBLIC-PROBES.lean.txt').read_bytes()
assert public.count(b'#print axioms ') == 15 and b'#check ' not in public
assert b'execute_returned_of_actual_prefixes' not in public
assert b'seeds_preserved_at_every_actual_query_endpoint' not in public
assert len(set(public_names)) == 15
imports = (control / 'IMPORTS.lean.txt').read_bytes()
assert len(re.findall(rb'^import ', imports, re.M)) == 8
assert {line.decode().removeprefix('import MicroCFTA.') for line in imports.splitlines()} == set(new_names)
new_audit = imports + old_audit + b'\n' + public
assert new_audit[stage['audit_old_block_offset']:stage['audit_old_block_offset'] + len(old_audit)] == old_audit
assert sha(new_audit) == stage['staged_audit_sha256']
assert len(re.findall(rb'^import ', new_audit, re.M)) == 5278
assert new_audit.count(b'#print axioms ') == 724
report = dict(stage)
report.update({'status': 'ACTUALLY STAGED BY ROOT AFTER VERIFIED TERMINAL PASS',
    'staged_at': datetime.datetime.now().astimezone().isoformat(),
    'actual_private_session': receipt['actual_session'], 'actual_terminal': True,
    'private_receipt_sha256': sha(receipt_path.read_bytes()),
    'private_checked_sha256': sha(checked_bytes), 'actual_pins_reverified': len(pins),
    'normal_Source_changed': True, 'published': False})
outputs = dict(snapshots)
outputs.update({work / 'SEED-CLOSURE-Audit-BEFORE.lean.txt': old_audit,
    work / 'SEED-CLOSURE-baseline-source-pins.json':
        (json.dumps({name: record['sha256'] for name, record in baseline['sources'].items()}, indent=2, sort_keys=True) + '\n').encode(),
    work / 'SOURCES-NORMAL-STAGING.json': (json.dumps(report, indent=2) + '\n').encode(),
    work / 'IMPORTS.lean.txt': imports,
    work / 'PUBLIC-PROBES.lean.txt': public})
for path, data in outputs.items():
    assert not path.exists() or path.read_bytes() == data, str(path)

# Root alone executes these writes after every preflight gate above passes.
for path, data in outputs.items():
    if not path.exists():
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(data)
for path, data in replacements.items():
    path.write_bytes(data)
(root / 'lean/MicroCFTA/Audit.lean').write_bytes(new_audit)
changed_old = {name for name in baseline['sources'] if root / name in replacements} | {'lean/MicroCFTA/Audit.lean'}
assert len(changed_old) == 6
for name, record in baseline['sources'].items():
    if name not in changed_old:
        verify(root / name, record)
assert len(baseline['sources']) - len(changed_old) == 6264
assert len(list((root / 'lean/MicroCFTA').glob('*.lean'))) == 6278
for path, data in replacements.items():
    assert path.read_bytes() == data
assert (root / 'lean/MicroCFTA/Audit.lean').read_bytes() == new_audit
print(json.dumps({'staged_new_modules': 8, 'changed_existing_owners': 5,
    'source_files': 6278, 'audit_imports': 5278, 'fresh_public_reports': 15,
    'audit_reports': 724, 'owning_private_reports_not_in_Audit': 2,
    'old_other_source_files_byte_exact': 6264,
    'actual_private_session': receipt['actual_session'],
    'joint_finite_completion_proved': False}))
