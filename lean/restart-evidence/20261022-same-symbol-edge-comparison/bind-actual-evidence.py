import ast
import difflib
import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
name = 'SourceCurrentSameSymbolEdgeComparison'
source = (HERE / (name + '.lean')).read_bytes()
sha = lambda data: hashlib.sha256(data).hexdigest()
assert sha(source) == '02d01576ce9e7188342835138452a5163b150e28c264c01782137848e1a1c560'
readback = json.loads((HERE / 'public-readback/same-symbol-edge-comparison-full-readback.json').read_text())
checked = (HERE / 'public-readback/same-symbol-edge-comparison-original_rows_complete-public-type.txt').read_bytes()
body = (HERE / 'public-readback/same-symbol-edge-comparison-original_rows_complete-body.txt').read_bytes()
assert readback['heads'][0]['actual_axioms'] == ['Classical.choice', 'Quot.sound', 'propext']
jobs = {}
for path in HERE.glob('*.json'):
    item = json.loads(path.read_text())
    if isinstance(item, dict) and 'wrapper' in item and 'exit_code' in item:
        if Path(item.get('command', [''])[0]).name in {'lean', 'lake'}:
            jobs[path.stem] = item
strict, full, audit_stem = ['same-symbol-edge-comparison-' + suffix
                          for suffix in ['strict-1', 'public-1', 'audit-1']]
assert set(jobs) == {strict, full, audit_stem}
assert all(item['exit_code'] == 0 for item in jobs.values())
assert (HERE / (strict + '.log')).read_bytes() == b''
audit = (HERE / (audit_stem + '.log')).read_bytes()
build = re.search(rb'Build completed successfully \((\d+) jobs\)\.', audit)
dependencies = re.search(rb'Checked axiom dependencies of (\d+) MicroCFTA theorems', audit)
assert build and dependencies and int(build[1]) > 0 and int(dependencies[1]) > 0
ledger = {}
for stem, receipt in jobs.items():
    raw = (HERE / receipt['log']).read_bytes()
    source_hash = receipt.get('sha256')
    errors = len(re.findall(rb'^.+?:\d+:\d+: error(?:\([^)]*\))?:', raw, re.M)) if source_hash else None
    warnings = len(re.findall(rb'^.+?:\d+:\d+: warning(?:\([^)]*\))?:', raw, re.M)) if source_hash else None
    ledger[stem] = [receipt['exit_code'], source_hash, sha(raw), errors, warnings]
assert all(row[3:] == [0, 0] for row in ledger.values() if row[1])
review = json.loads((HERE / 'root-full-review.json').read_text())
assert review['status'] == 'ROOT_ACCEPTED_FOR_OFFICIAL_INSTALL_AND_AUDIT'
assert review['complete_public_type_root_review'] == review['independent_complete_public_type_review'] == 'CLEAR'
values = {
    'SOURCE_SHA': sha(source), 'SELECTED_SOURCE_SHA': sha(source),
    'SOURCE_LINES': str(len(source.splitlines())),
    'STRICT_STEM': strict, 'SELECTED_STRICT_STEM': strict,
    'FULL_STEM': full, 'SELECTED_FULL_STEM': full, 'AUDIT_STEM': audit_stem,
    'ACTUAL_JOBS': str(len(jobs)),
    'SOURCE_JOBS': str(sum(bool(row[1]) for row in ledger.values())),
    'AUDIT_JOBS': str(sum(not row[1] for row in ledger.values())),
    'FAILED_JOBS': str(sum(row[0] != 0 for row in ledger.values())),
    'WARNED_SOURCE_EXIT_ZERO_JOBS': str(sum(row[0] == 0 and bool(row[1]) and bool(row[4]) for row in ledger.values())),
    'REJECTED_PUBLIC_TYPE_JOBS': '0', 'REJECTED_PUBLIC_STEMS_JSON': '[]',
    'JOBS_JSON': json.dumps(ledger, sort_keys=True),
    'AUDIT_BUILD_JOBS': build[1].decode(), 'AUDIT_DEPENDENCIES': dependencies[1].decode(),
    'AUDIT_SHA': sha(audit), 'FULL_RAW_SHA': readback['log_sha256'],
    'FULL_RAW_BYTES': str(readback['log_bytes']),
    'TYPE_SHA': sha(checked), 'PUBLIC_TYPE_SHA': sha(checked),
    'TYPE_LOGICAL_LINES': str(len(checked.splitlines())),
    'TYPE_LINE_FEEDS': str(checked.count(b'\n')), 'TYPE_BYTES': str(len(checked)),
    'TYPE_CHARACTERS': str(len(checked.decode())),
    'BODY_BYTES': str(len(body)), 'BODY_CHARACTERS': str(len(body.decode())),
    'ACTUAL_AXIOMS_JSON': json.dumps(readback['heads'][0]['actual_axioms']),
    'BACKUP_REF': 'codex/backup-same-symbol-edge-comparison-20261022-0424',
    'FULL_READER_SHA': sha((HERE / 'full-preparation/check-full-public.py').read_bytes()),
}
sets = [
    ('checkpoint-preparation', 'actual-tools-preparation', [
        'verify-preservation.py', 'verify-checkpoint.py', 'commit-proofs.py',
        'seal-checkpoint.py', 'verify-seal.py', 'archive-support.py',
        'final-publication.py', 'update-documents.py'], 18),
    ('proof-verifier-preparation', 'actual-verifier-preparation', ['verify-proofs.py'], 25),
]
for predecessor, directory, names, expected_bindings in sets:
    target = HERE / directory
    assert not target.exists()
    target.mkdir()
    pins, patches, used = {}, [], {}
    for name in names:
        path = HERE / predecessor / name
        before = path.read_text()
        after = before
        for key in sorted(set(re.findall(r'__H14_([A-Z_]+)__', before))):
            token, value = '__H14_' + key + '__', values[key]
            if key.endswith('_JSON'):
                after = after.replace('"' + token + '"', repr(value)).replace("'" + token + "'", repr(value))
            else:
                after = after.replace(token, value)
            assert token not in after
            used[key] = value
        assert '__H14_' not in after
        ast.parse(after)
        assert sum(isinstance(node, ast.Assert) for node in ast.walk(ast.parse(before))) == sum(
            isinstance(node, ast.Assert) for node in ast.walk(ast.parse(after)))
        (target / name).write_text(after)
        pins[name] = sha(after.encode())
        patches.extend(difflib.unified_diff(before.splitlines(True), after.splitlines(True),
            fromfile=str(path.relative_to(HERE)), tofile=directory + '/' + name))
    assert len(used) == expected_bindings
    (target / 'binding.patch').write_text(''.join(patches))
    (target / 'bindings.json').write_text(json.dumps(used, indent=2) + '\n')
    (target / 'pins.json').write_text(json.dumps(pins, indent=2) + '\n')
    print(json.dumps({'status': 'BOUND_NOT_ACTIVATED', 'directory': directory,
                      'files': len(pins), 'bindings': len(used), 'pins': pins}))
