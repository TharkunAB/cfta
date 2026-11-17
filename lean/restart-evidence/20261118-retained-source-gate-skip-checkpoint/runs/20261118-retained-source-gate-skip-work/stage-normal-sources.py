from pathlib import Path
import hashlib
import json

root = Path('/home/tritlo/Code/mcfta')
base = root / 'lean/restart-evidence'
control = base / '20261118-retained-source-gate-skip-staging-control-draft'
work = base / '20261118-retained-source-gate-skip-work'
sha = lambda data: hashlib.sha256(data).hexdigest()
assert Path(__file__).resolve().parent == work.resolve()
assert Path(__file__).read_bytes() == (control / 'stage-normal-sources.py').read_bytes()

def verify(path, record):
    data = path.read_bytes()
    assert sha(data) == (record['sha256'] if isinstance(record, dict) else record), str(path)
    if isinstance(record, dict) and 'bytes' in record:
        assert len(data) == record['bytes'], str(path)
    return data

for name, record in json.loads((control / 'MANIFEST.json').read_text())['files'].items():
    verify(control / name, record)
for name, record in json.loads((control / 'ACTUAL-INPUT-PINS.json').read_text()).items():
    verify(root / name, record)
stage = json.loads((control / 'EXPECTED-STAGE.json').read_text())
private_control = base / stage['private_control']
verify(private_control / 'MANIFEST.json', stage['private_control_manifest_sha256'])
selected_bytes = verify(private_control / 'SELECTION.json', stage['private_selection_sha256'])
assert selected_bytes == (control / 'CHECK-SELECTION.json').read_bytes()
selected = json.loads(selected_bytes)
run = base / stage['private_run']
receipt = json.loads((work / stage['private_verified_receipt']).read_text())
assert receipt['actual_session'] == stage['actual_private_session'] == 15994
assert receipt['actual_terminal'] and receipt['actual_terminal_exit'] == 0
assert receipt['runtime'] == run.name and receipt['source_baseline'] == stage['source_baseline']
checked = json.loads(verify(run / 'checked.json', receipt['checked_sha256']))
assert json.loads(verify(run / 'results.json', receipt['results_sha256'])) == checked
assert receipt['checks'] == checked['checks'] and all(checked['passed'])
assert checked['two_components_checked'] and checked['proof_credit'] and checked['source_pins_unchanged']
assert checked['both_selected_FIRST_headers_exact'] and checked['old_gate_owner_prefix_byte_exact']
assert checked['actual_printed_public_axiom_reports'] == 2 and checked['actual_definition_declaration_checks'] == 0
assert checked['limits'] == {'memory.max': '8589934592', 'memory.high': '8589934592', 'memory.swap.max': '0'}
assert [x['name'] for x in checked['checks']] == stage['compile_order']
assert all(x['exit'] == 0 and x['total_axiom_reports'] == 1 and not x['diagnostics']
    and not x['nonstandard_axioms'] and not x['sorryAx'] for x in checked['checks'])
run_pins = json.loads(verify(run / 'source-pins.json', receipt['source_pins_sha256']))
assert len(run_pins) == receipt['pins_independently_reverified'] == 6338
for name, digest in run_pins.items():
    verify(root / name, digest)
baseline_path = root / stage['source_baseline_path']
baseline = json.loads(verify(baseline_path, stage['source_baseline_sha256']))
assert len(baseline['sources']) == 6278
assert {str(p.relative_to(root)) for p in (root / 'lean/MicroCFTA').glob('*.lean')} == set(baseline['sources'])
for name, record in {**baseline['sources'], **baseline['toolchain']}.items():
    verify(root / name, record)
# Normal Source staging requires the prior checkpoint's actual verified push.
push = json.loads((root / stage['prior_checkpoint_push_receipt']).read_text())
assert push['source_commit'] == stage['source_baseline']
assert push['checkpoint_commit'] == push['remote_commit']
assert push['actual_push_terminal'] and push['actual_push_terminal_exit'] == 0
assert push['actual_remote_check_terminal'] and push['actual_remote_check_terminal_exit'] == 0
assert push['postpush_current_tree_verifier_terminal_exit'] == 0
assert push['normal_Source_files'] == 6278
old_audit = verify(root / 'lean/MicroCFTA/Audit.lean', {'sha256': stage['old_audit_sha256'], 'bytes': stage['old_audit_bytes']})
assert old_audit.count(b'#print axioms ') == 724
assert sum(line.startswith(b'import ') for line in old_audit.splitlines()) == 5278
replacements = {}
snapshots = {}
public = b''
for item, original in zip(stage['components'], selected['components']):
    assert all(item[name] == value for name, value in original.items())
    packet = base / item['packet']
    manifest = json.loads(verify(packet / 'MANIFEST.json', item['manifest_sha256']))
    for name, record in manifest['files'].items():
        verify(packet / name, record)
    for name in ['SOURCE-PINS.json', 'DEPENDENCY-PINS.json']:
        if (packet / name).exists():
            for path, record in json.loads((packet / name).read_text()).items():
                verify(root / path, record)
    raw = verify(packet / item['source'], {'sha256': item['raw_sha256'], 'bytes': item['raw_bytes']})
    probe = verify(packet / item['probe'], item['probe_sha256'])
    assert (run / 'source/MicroCFTA' / (item['module'] + '.lean')).read_bytes() == raw + b'\n' + probe
    assert probe.count(b'#print axioms ') == 1 and b'#check ' not in probe
    target = root / item['source_path']
    if item['kind'] == 'existing_owner_EOF':
        before = verify(target, {'sha256': item['owner_sha256'], 'bytes': item['owner_bytes']})
        assert raw == before + verify(packet / item['append'], item['append_sha256'])
        snapshots[root / item['old_snapshot']] = before
    else:
        assert item['kind'] == 'new_module' and not target.exists() and not target.is_symlink()
    header = verify(packet / item['header'], item['header_sha256'])
    start = raw.index(header.splitlines()[0])
    assert raw[start:raw.index(b' := by', start)].rstrip() == header.rstrip()
    replacements[target] = raw
    public += probe
imports = (control / 'EXPECTED-IMPORTS.lean.txt').read_bytes()
assert imports == b'import MicroCFTA.SourceSynthesisCurrentRetainedSharedEmptySkip\n'
assert len(imports) == stage['audit_old_block_offset']
assert public == (control / 'EXPECTED-PUBLIC-PROBES.lean.txt').read_bytes()
assert public.count(b'#print axioms ') == 2
outputs = dict(snapshots)
outputs.update({
    work / 'Audit-BEFORE.lean.txt': old_audit,
    work / 'baseline-source-pins.json': (json.dumps({name: record['sha256'] for name, record in baseline['sources'].items()}, indent=2, sort_keys=True) + '\n').encode(),
    work / 'SOURCES-NORMAL-STAGING.json': (control / 'EXPECTED-STAGE.json').read_bytes(),
    work / 'IMPORTS.lean.txt': imports,
    work / 'PUBLIC-PROBES.lean.txt': public,
})
assert not (work / 'SOURCES-NORMAL-STAGING.json').exists(), 'Do not stage the same batch twice.'
for path, data in outputs.items():
    assert not path.exists() or path.read_bytes() == data, str(path)
# Root reviews and executes this phase after every read-only preflight passes.
for path, data in outputs.items():
    if not path.exists():
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(data)
for path, data in replacements.items():
    path.write_bytes(data)
(root / 'lean/MicroCFTA/Audit.lean').write_bytes(imports + old_audit + b'\n' + public)
changed = {str(path.relative_to(root)) for path in replacements} | {'lean/MicroCFTA/Audit.lean'}
assert len(set(baseline['sources']) - changed) == 6276
for name, record in baseline['sources'].items():
    if name not in changed:
        verify(root / name, record)
audit = (root / 'lean/MicroCFTA/Audit.lean').read_bytes()
assert audit[len(imports):len(imports) + len(old_audit)] == old_audit
assert audit.count(b'#print axioms ') == 726
assert sum(line.startswith(b'import ') for line in audit.splitlines()) == 5279
assert len(list((root / 'lean/MicroCFTA').glob('*.lean'))) == 6279
print(json.dumps({'staged_components': 2, 'source_files': 6279, 'audit_imports': 5279,
    'audit_reports': 726, 'fresh_reports': 2, 'inherited_reports': 518,
    'combined_reports': 520, 'old_gate_prefix_byte_exact': True,
    'old_other_Source_files_byte_exact': 6276, 'normal_Source_changed': True}))
