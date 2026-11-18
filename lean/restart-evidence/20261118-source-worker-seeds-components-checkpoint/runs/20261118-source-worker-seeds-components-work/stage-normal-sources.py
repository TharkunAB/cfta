from pathlib import Path
import datetime
import hashlib
import json
import re
import subprocess

ROOT = Path('/home/tritlo/Code/mcfta')
BASE = ROOT / 'lean/restart-evidence'
CONTROL = BASE / '20261118-source-worker-seeds-components-staging-control-draft'
WORK = BASE / '20261118-source-worker-seeds-components-work'
SHA = lambda data: hashlib.sha256(data).hexdigest()
assert Path(__file__).resolve().parent == WORK.resolve(), 'Root reviews and copies this staging controller.'
assert Path(__file__).read_bytes() == (CONTROL / 'stage-normal-sources.py').read_bytes()
assert not (WORK / 'SOURCES-NORMAL-STAGING.json').exists(), 'Do not stage twice.'


def verify(path, record):
    data = path.read_bytes()
    digest = record['sha256'] if isinstance(record, dict) else record
    assert SHA(data) == digest, str(path)
    if isinstance(record, dict) and 'bytes' in record:
        assert len(data) == record['bytes'], str(path)
    return data


def records(manifest):
    files = manifest['files']
    return files.items() if isinstance(files, dict) else [(item.get('file', item.get('path')), item) for item in files]


for name, record in records(json.loads((CONTROL / 'MANIFEST.json').read_text())):
    verify(CONTROL / name, record)
for name, record in json.loads((CONTROL / 'ACTUAL-INPUT-PINS.json').read_text()).items():
    verify(ROOT / name, record)
stage = json.loads((CONTROL / 'EXPECTED-STAGE.json').read_text())
assert stage['status'] == 'FROZEN_STAGING_CANDIDATE; NOT_EXECUTED'
assert stage['source_baseline'] == 'fc345af6e51dd1e813fed83423f25c3228b78874'
assert len(stage['components']) == 5 and len(stage['private_subsets']) == 2
assert stage['fresh_reports'] == stage['new_public_theorems'] == 7
assert stage['new_private_helpers_transitive'] == 7 and stage['new_Prop_definitions'] == 0
assert stage['explicit_private_reports'] == stage['definition_checks'] == 0
assert stage['inherited_reports'] == 520 and stage['combined_reports'] == 527
assert stage['resource_owner_reports_inherited'] == 264 and stage['fresh_credit_for_old_owner_theorems'] == 0
component_by_module = {item['module']: item for item in stage['components']}
assert len(component_by_module) == 5 and stage['compile_order'] == list(component_by_module)
subset_modules = []
subset_receipts = []
for subset in stage['private_subsets']:
    controller = BASE / subset['control']
    verify(controller / 'MANIFEST.json', subset['control_manifest_sha256'])
    selection_bytes = verify(controller / 'SELECTION.json', subset['selection_sha256'])
    assert selection_bytes == (CONTROL / subset['selection_copy']).read_bytes()
    selection = json.loads(selection_bytes)
    assert selection['source_commit'] == stage['source_baseline'] and selection['source_files'] == 6279
    assert selection['compile_order'] == subset['modules']
    assert len(selection['components']) == len(subset['modules'])
    run = BASE / subset['runtime']
    assert selection['runtime'] == run.name
    receipt = json.loads(verify(ROOT / subset['verified_receipt'], subset['verified_receipt_sha256']))
    assert type(receipt['actual_session']) is int and receipt['actual_session'] > 0
    assert receipt['actual_session'] == subset['actual_session']
    assert receipt['actual_terminal'] and receipt['actual_terminal_exit'] == 0
    assert receipt['runtime'] == run.name and receipt['source_baseline'] == stage['source_baseline']
    checked_bytes = verify(run / 'checked.json', receipt['checked_sha256'])
    checked = json.loads(checked_bytes)
    assert json.loads(verify(run / 'results.json', receipt['results_sha256'])) == checked
    assert checked['checks'] == receipt['checks'] == json.loads((run / 'checks.json').read_text())
    assert len(checked['passed']) == len(subset['modules']) and all(checked['passed'])
    assert checked['failure'] is None and checked['source_pins_unchanged'] and checked['proof_credit']
    assert not checked.get('normal_Source_changed', checked.get('normal_source_changed')) and not checked['published']
    assert checked['limits'] == {'memory.max': '8589934592', 'memory.high': '8589934592', 'memory.swap.max': '0'}
    assert [item['name'] for item in checked['checks']] == subset['modules']
    for result, chosen in zip(checked['checks'], selection['components']):
        item = component_by_module[result['name']]
        assert item['manifest_sha256'] == chosen['manifest_sha256']
        assert item['raw_sha256'] == chosen['raw_sha256'] and item['packet'] == chosen['packet']
        if 'headers' in chosen:
            assert item['headers'] == chosen['headers']
        else:
            assert {'file': chosen['header'], 'sha256': chosen['header_sha256']} in item['headers']
        assert item['probe_sha256'] == chosen['probe_sha256']
        assert result['exit'] == 0 and not result['diagnostics'] and not result['sorryAx'] and not result['nonstandard_axioms']
        assert result['total_axiom_reports'] == item['expected_axiom_reports']
        assert result['declaration_checks'] == item['expected_declaration_checks'] == 0
        packet = BASE / item['packet']
        fixture = run / 'source/MicroCFTA' / (item['module'] + '.lean')
        assert fixture.read_bytes() == (packet / item['source']).read_bytes() + b'\n' + (packet / item['probe']).read_bytes()
    pin_bytes = verify(run / 'source-pins.json', receipt['source_pins_sha256'])
    pins = json.loads(pin_bytes)
    assert receipt['pins_independently_reverified'] == len(pins) > 0
    for name, digest in pins.items():
        verify(ROOT / name, digest)
    subset_modules.extend(subset['modules'])
    subset_receipts.append({'runtime': run.name, 'actual_session': receipt['actual_session'],
        'verified_receipt_sha256': SHA((ROOT / subset['verified_receipt']).read_bytes()),
        'checked_sha256': SHA(checked_bytes), 'actual_pins_reverified': len(pins),
        'public_reports': sum(item['total_axiom_reports'] for item in checked['checks'])})
assert subset_modules == stage['compile_order']
assert sum(item['public_reports'] for item in subset_receipts) == 7

# Normal staging requires the actual prior pushed checkpoint, not a future promise.
push = json.loads((ROOT / stage['prior_checkpoint_push_receipt']).read_text())
assert push['source_commit'] == stage['source_baseline']
assert push['checkpoint_commit'] == push['remote_commit'] == stage['prior_checkpoint']
assert push['actual_push_terminal'] and push['actual_push_terminal_exit'] == 0
assert push['actual_remote_check_terminal'] and push['actual_remote_check_terminal_exit'] == 0
assert push['postpush_current_tree_verifier_terminal_exit'] == 0 and push['normal_Source_files'] == 6279
subprocess.run(['git', 'merge-base', '--is-ancestor', push['checkpoint_commit'], 'HEAD'], cwd=ROOT, check=True)
subprocess.run(['git', 'diff', '--quiet', stage['source_baseline'], 'HEAD', '--',
    'lean/MicroCFTA', 'lean/lake-manifest.json', 'lean/lakefile.toml', 'lean/lean-toolchain', 'shell.nix'], cwd=ROOT, check=True)
baseline = json.loads(verify(ROOT / stage['source_baseline_path'], stage['source_baseline_sha256']))
assert baseline['source_commit'] == stage['source_baseline'] and len(baseline['sources']) == 6279
assert {str(p.relative_to(ROOT)) for p in (ROOT / 'lean/MicroCFTA').glob('*.lean')} == set(baseline['sources'])
for name, record in {**baseline['sources'], **baseline['toolchain']}.items():
    verify(ROOT / name, record)
old_audit = verify(ROOT / 'lean/MicroCFTA/Audit.lean',
    {'sha256': stage['old_audit_sha256'], 'bytes': stage['old_audit_bytes']})
assert old_audit.count(b'#print axioms ') == 726
assert sum(line.startswith(b'import ') for line in old_audit.splitlines()) == 5279
replacements = {}
snapshots = {}
new_names = []
public_names = []
raws = {}
for item in stage['components']:
    packet = BASE / item['packet']
    manifest = json.loads(verify(packet / 'MANIFEST.json', item['manifest_sha256']))
    for name, record in records(manifest):
        verify(packet / name, record)
    raw = verify(packet / item['source'], {'sha256': item['raw_sha256'], 'bytes': item['raw_bytes']})
    if item['kind'] == 'existing_owner_import_and_EOF':
        before = verify(ROOT / item['owner_source'], {'sha256': item['owner_sha256'], 'bytes': item['owner_bytes']})
        imported = verify(packet / item['imports'], item['imports_sha256'])
        appended = verify(packet / item['append'], item['append_sha256'])
        assert len(before) == 23529 and len(imported) == item['owner_offset'] == 61
        assert raw == imported + before + appended
        snapshots[ROOT / item['old_snapshot']] = before
        declarations = appended
    else:
        assert item['kind'] == 'new_module'
        assert not (ROOT / item['source_path']).exists() and not (ROOT / item['source_path']).is_symlink()
        new_names.append(item['module'])
        declarations = raw
    assert b'#print axioms ' not in raw and b'#check ' not in raw
    assert not re.search(rb'set_option\s+(?:maxHeartbeats|maxRecDepth|warningAsError|linter\.)', declarations)
    for header in item['headers']:
        text = verify(packet / header['file'], header['sha256'])
        assert declarations.count(text.rstrip(b'\n')) == 1
    probe = verify(packet / item['probe'], item['probe_sha256'])
    assert re.findall(r'^#print axioms (\S+)', probe.decode(), re.M) == item['public_qnames']
    assert probe.count(b'#check ') == 0
    assert re.findall(r'^theorem (\w+)', declarations.decode(), re.M) == [q.rsplit('.', 1)[1] for q in item['public_qnames']]
    assert len(re.findall(r'^private theorem (\w+)', declarations.decode(), re.M)) == item['new_private_helpers_transitive']
    assert not re.findall(r'^(?:private )?(?:def|inductive|structure) ', declarations.decode(), re.M)
    assert not (ROOT / item['source_path']).is_symlink()
    replacements[ROOT / item['source_path']] = raw
    raws[item['module']] = raw
    public_names.extend(item['public_qnames'])
assert len(new_names) == 4 and len(replacements) == 5 and len(public_names) == len(set(public_names)) == 7
assert sum(item['new_private_helpers_transitive'] for item in stage['components']) == 7
public = b''.join(('#print axioms ' + name + '\n').encode() for name in public_names)
assert public == (CONTROL / 'PUBLIC-PROBES.lean.txt').read_bytes()
assert all(name.encode() not in old_audit for name in public_names)
imports = (CONTROL / 'IMPORTS.lean.txt').read_bytes()
assert imports == b''.join(('import MicroCFTA.' + name + '\n').encode() for name in new_names)
assert len(imports) == stage['audit_old_block_offset'] == 287
new_audit = imports + old_audit + b'\n' + public
assert SHA(new_audit) == stage['staged_audit_sha256'] and len(new_audit) == stage['staged_audit_bytes']
assert new_audit[len(imports):len(imports) + len(old_audit)] == old_audit
assert new_audit.count(b'#print axioms ') == 733 and sum(line.startswith(b'import ') for line in new_audit.splitlines()) == 5283

# Recheck the full five-output import graph before any Source write.
module_sources = {p.stem: p.read_bytes() for p in (ROOT / 'lean/MicroCFTA').glob('*.lean')}
module_sources.update(raws)
graph = {name: re.findall(r'^import MicroCFTA\.([A-Za-z0-9_]+)\s*$', data.decode(), re.M)
    for name, data in module_sources.items()}
order = []
active = []
visited = set()


def visit(name):
    assert name not in active, 'Import cycle: ' + repr(active + [name])
    if name in visited:
        return
    active.append(name)
    for dependency in graph[name]:
        assert dependency in graph, (name, dependency)
        visit(dependency)
    active.pop()
    visited.add(name)
    order.append(name)


for name in stage['compile_order']:
    visit(name)
topological = json.loads((CONTROL / 'TOPOLOGICAL-ORDER.json').read_text())
assert order == topological['full_transitive_order'] and len(order) == 2394
assert {name: graph[name] for name in order} == topological['direct_imports']
assert [name for name in order if name in raws] == stage['compile_order']
report = dict(stage)
report.update({'status': 'ACTUALLY STAGED BY ROOT AFTER BOTH VERIFIED SUBSETS',
    'staged_at': datetime.datetime.now().astimezone().isoformat(),
    'actual_private_subsets': subset_receipts, 'normal_Source_changed': True, 'published': False})
outputs = dict(snapshots)
outputs.update({WORK / 'Audit-BEFORE.lean.txt': old_audit,
    WORK / 'baseline-source-pins.json': (json.dumps({name: record['sha256'] for name, record in baseline['sources'].items()}, indent=2, sort_keys=True) + '\n').encode(),
    WORK / 'SOURCES-NORMAL-STAGING.json': (json.dumps(report, indent=2) + '\n').encode(),
    WORK / 'IMPORTS.lean.txt': imports, WORK / 'PUBLIC-PROBES.lean.txt': public})
for path, data in outputs.items():
    assert not path.exists() or path.read_bytes() == data, str(path)

# Root alone executes the writes below, after every receipt, pin and graph gate.
for path, data in outputs.items():
    if not path.exists():
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(data)
for path, data in replacements.items():
    path.write_bytes(data)
(ROOT / 'lean/MicroCFTA/Audit.lean').write_bytes(new_audit)
assert len(list((ROOT / 'lean/MicroCFTA').glob('*.lean'))) == 6283
changed_old = {str(path.relative_to(ROOT)) for path in replacements if str(path.relative_to(ROOT)) in baseline['sources']}
changed_old.add('lean/MicroCFTA/Audit.lean')
assert changed_old == {'lean/MicroCFTA/SourceCurrentNativeNumericalSeedClosure.lean', 'lean/MicroCFTA/Audit.lean'}
assert len(baseline['sources']) - len(changed_old) == 6277
for name, record in baseline['sources'].items():
    if name not in changed_old:
        verify(ROOT / name, record)
for path, data in replacements.items():
    assert path.read_bytes() == data
assert (ROOT / 'lean/MicroCFTA/Audit.lean').read_bytes() == new_audit
print(json.dumps({'staged_components': 5, 'new_modules': 4, 'changed_existing_owner_modules': 1,
    'source_files': 6283, 'audit_imports': 5283, 'audit_reports': 733, 'independent_reports': 328,
    'fresh_public_reports': 7, 'inherited_reports': 520, 'combined_reports': 527,
    'new_private_helpers_transitive': 7, 'explicit_private_reports': 0, 'definitions': 0,
    'old_owner_bytes': 23529, 'old_owner_offset': 61, 'old_audit_bytes_preserved': len(old_audit),
    'other_old_Source_files_exact': 6277, 'actual_private_subsets': subset_receipts,
    'normal_Source_changed': True, 'published': False, 'joint_finite_completion_proved': False}))
