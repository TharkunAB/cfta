import ast
import difflib
import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
source = (HERE / 'SourceCurrentAllocatedDirectEdgeWordRanges.lean').read_bytes()
assert hashlib.sha256(source).hexdigest() == 'de874220ae0aab490300f809c9fa4d2a931030fd69b95efb70deaa9a92a4b440'
readback = json.loads((HERE / 'public-readback/direct-edge-word-ranges-full-readback.json').read_text())
checked = (HERE / 'public-readback/direct-edge-word-ranges-edge_body-public-type.txt').read_bytes()
body = (HERE / 'public-readback/direct-edge-word-ranges-edge_body-body.txt').read_bytes()
assert readback['heads'][0]['actual_axioms'] == ['Classical.choice', 'Quot.sound', 'propext']
jobs = {}
for path in HERE.glob('*.json'):
    item = json.loads(path.read_text())
    if isinstance(item, dict) and 'wrapper' in item and 'exit_code' in item:
        if Path(item.get('command', [''])[0]).name in {'lean', 'lake'}:
            jobs[path.stem] = item
assert set(jobs) == {'direct-edge-word-ranges-strict-1', 'direct-edge-word-ranges-public-1', 'direct-edge-word-ranges-audit-1'}
assert all(item['exit_code'] == 0 for item in jobs.values())
assert (HERE / 'direct-edge-word-ranges-strict-1.log').read_bytes() == b''
audit = (HERE / 'direct-edge-word-ranges-audit-1.log').read_bytes()
build_jobs = re.search(rb'Build completed successfully \((\d+) jobs\)\.', audit)
dependencies = re.search(rb'Checked axiom dependencies of (\d+) MicroCFTA theorems', audit)
assert build_jobs and dependencies
assert (int(build_jobs[1]), int(dependencies[1])) == (3629, 75380)
values = {
    'SOURCE_SHA': hashlib.sha256(source).hexdigest(), 'SOURCE_LINES': str(len(source.splitlines())),
    'SELECTED_STRICT': 'direct-edge-word-ranges-strict-1', 'SELECTED_FULL': 'direct-edge-word-ranges-public-1',
    'AUDIT_STEM': 'direct-edge-word-ranges-audit-1',
    'ACTUAL_JOBS': '3', 'SOURCE_JOBS': '2', 'AUDIT_JOBS': '1', 'FAILED_JOBS': '0',
    'WARNED_SOURCE_EXIT_ZERO_JOBS': '0', 'REJECTED_PUBLIC_TYPE_JOBS': '0',
    'AUDIT_BUILD_JOBS': build_jobs[1].decode(), 'AUDIT_DEPENDENCIES': dependencies[1].decode(),
    'AUDIT_SHA': hashlib.sha256(audit).hexdigest(), 'AUDIT_RAW_SHA': hashlib.sha256(audit).hexdigest(),
    'FULL_SOURCE_SHA': jobs['direct-edge-word-ranges-public-1']['sha256'],
    'FULL_RAW_SHA': readback['log_sha256'], 'FULL_RAW_BYTES': str(readback['log_bytes']),
    'TYPE_SHA': hashlib.sha256(checked).hexdigest(), 'TYPE_LINES': str(len(checked.splitlines())),
    'TYPE_LF': str(checked.count(b'\n')), 'TYPE_BYTES': str(len(checked)),
    'TYPE_CHARACTERS': str(len(checked.decode())), 'BODY_BYTES': str(len(body)),
    'BODY_CHARACTERS': str(len(body.decode())),
    'ACTUAL_AXIOMS_JSON': json.dumps(readback['heads'][0]['actual_axioms']),
    'TYPE_REVIEW_STATUS': 'ROOT_AND_INDEPENDENT_COMPLETE',
}
sets = [
    ('checkpoint-preparation', 'actual-tools-preparation', [
        'verify-preservation.py', 'verify-checkpoint.py', 'commit-proofs.py',
        'seal-checkpoint.py', 'verify-seal.py', 'archive-support.py',
        'final-publication.py', 'update-documents.py']),
    ('proof-verifier-preparation', 'actual-verifier-preparation', ['verify-proofs.py']),
]
for predecessor, directory, names in sets:
    target = HERE / directory
    assert not target.exists()
    target.mkdir()
    pins, patches, used = {}, [], {}
    for name in names:
        path = HERE / predecessor / name
        if name == 'update-documents.py':
            path = HERE / 'documents-preparation-v2/update-documents.py'
        before = path.read_text()
        after = before
        tokens = set(re.findall(r'__H12_([A-Z_]+)__', before))
        for key in sorted(tokens):
            value = values[key]
            token = '__H12_' + key + '__'
            if key == 'ACTUAL_AXIOMS_JSON':
                occurrences = after.count(token)
                after = after.replace('"' + token + '"', repr(value)).replace("'" + token + "'", repr(value))
                assert token not in after and occurrences > 0
            else:
                after = after.replace(token, value)
            used[key] = value
        assert '__H12_' not in after
        ast.parse(after)
        assert sum(isinstance(node, ast.Assert) for node in ast.walk(ast.parse(before))) == sum(
            isinstance(node, ast.Assert) for node in ast.walk(ast.parse(after)))
        (target / name).write_text(after)
        pins[name] = hashlib.sha256(after.encode()).hexdigest()
        patches.extend(difflib.unified_diff(before.splitlines(True), after.splitlines(True),
            fromfile=str(path.relative_to(HERE)), tofile=directory + '/' + name))
    assert len(used) == (18 if predecessor == 'checkpoint-preparation' else 22)
    (target / 'binding.patch').write_text(''.join(patches))
    (target / 'bindings.json').write_text(json.dumps(used, indent=2) + '\n')
    (target / 'pins.json').write_text(json.dumps(pins, indent=2) + '\n')
    print(json.dumps({'status': 'BOUND_NOT_ACTIVATED', 'directory': directory,
                      'files': len(pins), 'bindings': len(used), 'pins': pins}))
