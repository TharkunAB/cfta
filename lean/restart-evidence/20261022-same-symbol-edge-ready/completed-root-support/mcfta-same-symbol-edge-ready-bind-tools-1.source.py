import difflib
import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
bindings = {
    '__H10_SOURCE_SHA__': '68d9ca87569a4bb4ad3d2df6e928c441a4e218bf54154c1da9f4d14de6b2c8aa',
    '__H10_SOURCE_LINES__': '192',
    '__H10_SELECTED_STRICT__': 'same-symbol-edge-ready-strict-2',
    '__H10_SELECTED_FULL__': 'same-symbol-edge-ready-public-1',
    '__H10_AUDIT_STEM__': 'same-symbol-edge-ready-audit-1',
    '__H10_AUDIT_SHA__': '18fafb8c4bb0d3de3e0c2b2f2adcbd433c1f3621f2035aaf79847fa80d113688',
    '__H10_AUDIT_BUILD_JOBS__': '3627',
    '__H10_AUDIT_DEPENDENCIES__': '75377',
    '__H10_ACTUAL_JOBS__': '4',
    '__H10_SOURCE_JOBS__': '3',
    '__H10_AUDIT_JOBS__': '1',
    '__H10_FAILED_JOBS__': '1',
    '__H10_WARNED_SOURCE_EXIT_ZERO_JOBS__': '0',
    '__H10_REJECTED_PUBLIC_TYPE_JOBS__': '0',
    '__H10_FULL_RAW_SHA__': 'ffc63200806cbf19fa84666b5b288f39a6f40d8167bf7d886d143a97a7499dfe',
    '__H10_TYPE_SHA__': '3318dd2a433532c6a7d313cf7b587303358e4f9092fe7d79523ef93ca6c44c69',
    '__H10_ACTUAL_AXIOMS_JSON__': '["Classical.choice", "Quot.sound", "propext"]',
    '__H10_TYPE_REVIEW_STATUS__': 'ROOT_AND_INDEPENDENT_COMPLETE',
}
audit = (HERE / 'same-symbol-edge-ready-audit-1.log').read_bytes()
assert hashlib.sha256(audit).hexdigest() == bindings['__H10_AUDIT_SHA__']
assert b'Build completed successfully (3627 jobs).' in audit and b'75377 MicroCFTA theorems' in audit
assert json.loads((HERE / 'same-symbol-edge-ready-audit-1.json').read_text())['exit_code'] == 0
assert (HERE / 'same-symbol-edge-ready-strict-2.log').read_bytes() == b''
review = json.loads((HERE / 'root-full-review.json').read_text())
assert review['source_sha256'] == bindings['__H10_SOURCE_SHA__']
assert review['complete_public_type_root_review'] == review['independent_complete_public_type_review'] == 'CLEAR'
target = HERE / 'actual-tools-preparation'
target.mkdir()
names = [
    'verify-preservation.py', 'verify-checkpoint.py', 'commit-proofs.py', 'seal-checkpoint.py',
    'verify-seal.py', 'archive-support.py', 'final-publication.py', 'update-documents.py',
]
pins, patches = {}, []
for name in names:
    source = HERE / 'checkpoint-preparation' / name
    before = source.read_text()
    after = before
    for token, value in bindings.items():
        after = after.replace(token, value)
    assert not re.search(r'__H10_[A-Z_]+__', after), name
    (target / name).write_text(after)
    pins[name] = hashlib.sha256(after.encode()).hexdigest()
    patches.extend(difflib.unified_diff(before.splitlines(True), after.splitlines(True),
        fromfile=str(source.relative_to(HERE)), tofile='actual-tools-preparation/' + name))
(target / 'binding.patch').write_text(''.join(patches))
(target / 'bindings.json').write_text(json.dumps(bindings, indent=2) + '\n')
(target / 'pins.json').write_text(json.dumps(pins, indent=2) + '\n')
print(json.dumps({'status': 'PASS', 'prepared_not_activated': pins}))
