from pathlib import Path
import hashlib
import json

root = Path('/home/tritlo/Code/mcfta')
base = root / 'lean/restart-evidence'
control = base / '20261117-warm-full-admission-identity-staging-control-draft'
work = base / '20261117-warm-full-admission-identity-work'
private_control = base / '20261117-warm-full-admission-identity-check-control-draft'
assert Path(__file__).resolve().parent == work.resolve()
assert Path(__file__).read_bytes() == (control / 'stage-normal-sources.py').read_bytes()
sha = lambda data: hashlib.sha256(data).hexdigest()
for name, record in json.loads((control / 'MANIFEST.json').read_text())['files'].items():
    assert sha((control / name).read_bytes()) == record['sha256'], name
for name, record in json.loads((control / 'SOURCE-PINS.json').read_text()).items():
    assert sha((root / name).read_bytes()) == record['sha256'], name
stage = json.loads((control / 'EXPECTED-STAGE.json').read_text())
selection = json.loads((private_control / 'SELECTION.json').read_text())
run = base / selection['runtime']
checked = json.loads((run / 'checked.json').read_text())
receipt = json.loads((work / 'PRIVATE-CHECK-VERIFIED.json').read_text())
assert receipt['actual_session'] == 72836 and receipt['actual_terminal'] and receipt['actual_terminal_exit'] == 0
assert receipt['checks'] == checked['checks'] and checked['two_owners_checked']
assert len(checked['checks']) == 2 and all(checked['passed'])
assert checked['actual_new_public_axiom_reports'] == 4
assert checked['actual_definition_declaration_checks'] == 0
assert checked['fresh_credit_for_old_owner_theorems'] == 0
assert checked['old_owner_prefixes_byte_exact'] and checked['source_pins_unchanged']
for name, digest in json.loads((run / 'source-pins.json').read_text()).items():
    assert sha((root / name).read_bytes()) == digest, name
baseline = json.loads((private_control / 'SOURCE-BASELINE-PINS.json').read_text())
sources = sorted((root / 'lean/MicroCFTA').glob('*.lean'))
assert len(sources) == 6267
assert {str(path.relative_to(root)) for path in sources} == set(baseline['sources'])
for name, record in {**baseline['sources'], **baseline['toolchain']}.items():
    assert sha((root / name).read_bytes()) == record['sha256'], name
push = json.loads((base / '20261117-warm-no-new-mu-work/PUSH-VERIFIED.json').read_text())
assert push['source_commit'] == stage['source_baseline']
assert push['checkpoint_commit'] == push['remote_commit'] == stage['prior_checkpoint']
assert push['actual_push_terminal_exit'] == push['actual_remote_check_terminal_exit'] == 0
assert push['postpush_current_tree_verifier_terminal_exit'] == 0
old_audit = (root / 'lean/MicroCFTA/Audit.lean').read_bytes()
assert len(old_audit) == stage['old_audit_bytes'] == 430100
assert sha(old_audit) == stage['old_audit_sha256']
assert old_audit.count(b'#print axioms ') == 698
public = b''
replacements = {}
snapshots = {}
for item, chosen in zip(stage['components'], selection['components']):
    for name, value in chosen.items():
        assert item[name] == value, (item['module'], name)
    packet = base / item['packet']
    assert sha((packet / 'MANIFEST.json').read_bytes()) == item['manifest_sha256']
    before = (root / item['owner_source']).read_bytes()
    assert len(before) == item['owner_bytes'] and sha(before) == item['owner_sha256']
    raw = (packet / item['source']).read_bytes()
    append = (packet / item['append']).read_bytes()
    probe = (packet / item['probe']).read_bytes()
    assert raw == before + append and sha(raw) == item['raw_sha256']
    assert sha(append) == item['append_sha256'] and sha(probe) == item['probe_sha256']
    assert (run / 'source/MicroCFTA' / (item['module'] + '.lean')).read_bytes() == raw + b'\n' + probe
    assert probe.count(b'#print axioms ') == 2 and b'#check ' not in probe
    for header in item['headers']:
        data = (packet / header['file']).read_bytes()
        assert sha(data) == header['sha256'] and data.rstrip(b'\n') in append
    replacements[root / item['source_path']] = raw
    snapshots[root / item['old_snapshot']] = before
    public += probe
assert public == (control / 'EXPECTED-PUBLIC-PROBES.lean.txt').read_bytes()
assert public.count(b'#print axioms ') == 4 and b'#check ' not in public
outputs = dict(snapshots)
outputs.update({
    work / 'Audit-BEFORE.lean.txt': old_audit,
    work / 'baseline-source-pins.json': (json.dumps({name: record['sha256']
        for name, record in baseline['sources'].items()}, indent=2, sort_keys=True) + '\n').encode(),
    work / 'SOURCES-NORMAL-STAGING.json': (control / 'EXPECTED-STAGE.json').read_bytes(),
    work / 'IMPORTS.lean.txt': b'',
    work / 'PUBLIC-PROBES.lean.txt': public,
})
for path, data in outputs.items():
    assert not path.exists() or path.read_bytes() == data, str(path)

# Root approves and executes this guarded staging phase.
for path, data in outputs.items():
    if not path.exists():
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(data)
for path, data in replacements.items():
    path.write_bytes(data)
(root / 'lean/MicroCFTA/Audit.lean').write_bytes(old_audit + b'\n' + public)
changed = {str(path.relative_to(root)) for path in replacements} | {'lean/MicroCFTA/Audit.lean'}
for name, record in baseline['sources'].items():
    if name not in changed:
        assert sha((root / name).read_bytes()) == record['sha256'], name
assert len(baseline['sources']) - len(changed) == 6264
assert (root / 'lean/MicroCFTA/Audit.lean').read_bytes().count(b'#print axioms ') == 702
print(json.dumps({'staged_owners': 2, 'source_files': 6267, 'new_public_reports': 4,
    'old_owner_prefixes_byte_exact': True, 'old_other_source_files_byte_exact': 6264,
    'audit_imports': 5267, 'audit_reports': 702, 'new_audit_imports': 0}))
