from pathlib import Path
import hashlib
import json

root = Path('/home/tritlo/Code/mcfta')
base = root / 'lean/restart-evidence'
control = base / '20261117-third-query-six-seed-staging-control-draft'
work = base / '20261117-third-query-node-seed-work'
sha = lambda data: hashlib.sha256(data).hexdigest()
assert Path(__file__).resolve().parent == work.resolve()
assert Path(__file__).read_bytes() == (control / 'stage-normal-sources.py').read_bytes()
manifest = json.loads((control / 'MANIFEST.json').read_text())
assert manifest['status'] == 'FROZEN CANDIDATE / NOT EXECUTED'
for name, record in manifest['files'].items():
    data = (control / name).read_bytes()
    assert sha(data) == record['sha256'] and len(data) == record['bytes'], name
for name, record in json.loads((control / 'SOURCE-PINS.json').read_text()).items():
    assert sha((root / name).read_bytes()) == record['sha256'], name
stage = json.loads((control / 'EXPECTED-STAGE.json').read_text())
private_control = base / stage['private_control']
selection = json.loads((private_control / 'SELECTION.json').read_text())
run = base / stage['private_run']
assert selection['runtime'] == run.name
checked = json.loads((run / 'checked.json').read_text())
receipt = json.loads((work / stage['private_check_verified_receipt']).read_text())
assert receipt['actual_session'] == stage['actual_private_session'] == 37551
assert receipt['actual_terminal'] and receipt['actual_terminal_exit'] == 0
assert receipt['pins_independently_reverified'] == stage['actual_private_pins'] == 6467
assert receipt['checks'] == checked['checks'] and checked['all_six_components_checked']
assert checked['proof_credit'] and checked['source_pins_unchanged']
assert len(checked['checks']) == 6 and all(checked['passed'])
assert [x['name'] for x in checked['checks']] == stage['compile_order']
assert [x['total_axiom_reports'] for x in checked['checks']] == [2, 1, 1, 1, 1, 1]
assert checked['limits'] == {'memory.max': '8589934592', 'memory.high': '8589934592', 'memory.swap.max': '0'}
assert checked['actual_new_public_axiom_reports'] == 7
assert checked['actual_definition_declaration_checks'] == 0
assert checked['new_private_helpers_compiled_transitively'] == 6
assert checked['fresh_credit_for_old_owner_theorems'] == 0
assert checked['all_three_old_owner_prefixes_byte_exact']
assert checked['all_selected_first_headers_exact']
assert checked['all_six_third_query_cache_seeds_proved'] and checked['exact_b4_joint_composition_checked']
for name, digest in json.loads((run / 'source-pins.json').read_text()).items():
    assert sha((root / name).read_bytes()) == digest, name
baseline_file = root / selection['source_baseline_path']
baseline = json.loads(baseline_file.read_text())
assert sha(baseline_file.read_bytes()) == selection['source_baseline_sha256']
sources = sorted((root / 'lean/MicroCFTA').glob('*.lean'))
assert len(sources) == 6267
assert {str(path.relative_to(root)) for path in sources} == set(baseline['sources'])
for name, record in {**baseline['sources'], **baseline['toolchain']}.items():
    assert sha((root / name).read_bytes()) == record['sha256'], name
push = json.loads((base / '20261117-warm-full-admission-identity-work/PUSH-VERIFIED.json').read_text())
assert push['source_commit'] == stage['source_baseline']
assert push['checkpoint_commit'] == push['remote_commit'] == stage['prior_checkpoint']
assert push['archive_manifest_sha256'] == stage['prior_archive_manifest_sha256']
assert push['actual_push_terminal_exit'] == push['actual_remote_check_terminal_exit'] == 0
assert push['postpush_current_tree_verifier_terminal_exit'] == 0
old_audit = (root / 'lean/MicroCFTA/Audit.lean').read_bytes()
assert len(old_audit) == stage['old_audit_bytes'] == 430643
assert sha(old_audit) == stage['old_audit_sha256']
assert old_audit.count(b'#print axioms ') == 702
chosen = {x['module']: x for x in selection['components']}
assert len(chosen) == 6
public = b''
replacements = {}
snapshots = {}
new_sources = set()
for item in stage['components']:
    for name, value in chosen[item['module']].items():
        assert item[name] == value, (item['module'], name)
    packet = base / item['packet']
    assert sha((packet / 'MANIFEST.json').read_bytes()) == item['manifest_sha256']
    raw = (packet / item['source']).read_bytes()
    assert sha(raw) == item['raw_sha256'] and len(raw) == item['raw_bytes']
    probe = (packet / item['probe']).read_bytes()
    assert sha(probe) == item['probe_sha256']
    assert (run / 'source/MicroCFTA' / (item['module'] + '.lean')).read_bytes() == raw + b'\n' + probe
    assert probe.count(b'#print axioms ') == item['expected_axiom_reports'] and b'#check ' not in probe
    target = root / item['source_path']
    if item['kind'] == 'existing_owner_EOF':
        before = target.read_bytes()
        assert len(before) == item['old_bytes'] and sha(before) == item['old_sha256']
        append = (packet / item['append']).read_bytes()
        assert raw == before + append and sha(append) == item['append_sha256']
        snapshots[root / item['old_snapshot']] = before
    else:
        assert item['kind'] == 'new_module'
        assert not target.exists() and not target.is_symlink(), target
        new_sources.add(item['source_path'])
    for header in item['headers']:
        data = (packet / header['file']).read_bytes()
        assert sha(data) == header['sha256'] and data.rstrip(b'\n') in raw
    replacements[target] = raw
    public += probe
imports = (control / 'EXPECTED-IMPORTS.lean.txt').read_bytes()
assert len(imports) == stage['old_audit_exact_offset'] == 195
assert imports.count(b'import ') == 3 and len(new_sources) == 3
assert public == (control / 'EXPECTED-PUBLIC-PROBES.lean.txt').read_bytes()
assert public.count(b'#print axioms ') == 7 and b'#check ' not in public
outputs = dict(snapshots)
outputs.update({
    work / 'Audit-BEFORE.lean.txt': old_audit,
    work / 'baseline-source-pins.json': (json.dumps({name: record['sha256']
        for name, record in baseline['sources'].items()}, indent=2, sort_keys=True) + '\n').encode(),
    work / 'SOURCES-NORMAL-STAGING.json': (control / 'EXPECTED-STAGE.json').read_bytes(),
    work / 'IMPORTS.lean.txt': imports,
    work / 'PUBLIC-PROBES.lean.txt': public,
})
for path, data in outputs.items():
    assert not path.exists() or path.read_bytes() == data, str(path)

# Root approves and executes this guarded staging phase only after final full-chain success.
for path, data in outputs.items():
    if not path.exists():
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(data)
for path, data in replacements.items():
    path.write_bytes(data)
(root / 'lean/MicroCFTA/Audit.lean').write_bytes(imports + old_audit + b'\n' + public)
changed = {str(path.relative_to(root)) for path in replacements} | {'lean/MicroCFTA/Audit.lean'}
for name, record in baseline['sources'].items():
    if name not in changed:
        assert sha((root / name).read_bytes()) == record['sha256'], name
assert len(baseline['sources']) - len(changed - new_sources) == 6263
assert len(list((root / 'lean/MicroCFTA').glob('*.lean'))) == 6270
assert (root / 'lean/MicroCFTA/Audit.lean').read_bytes().count(b'#print axioms ') == 709
print(json.dumps({'staged_components': 6, 'source_files': 6270, 'new_public_reports': 7,
    'all_three_old_owner_prefixes_byte_exact': True, 'old_other_source_files_byte_exact': 6263,
    'audit_imports': 5270, 'audit_reports': 709, 'new_audit_imports': 3}))
