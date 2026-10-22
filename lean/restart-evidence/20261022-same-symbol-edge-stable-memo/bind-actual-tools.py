import difflib
import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
bindings = {
    '__H9_SOURCE_SHA256__': '6c96e7e8d5cb32d1209818ed65de83a5104b6a409d65b9caffb52d802e874b91',
    '__H9_SOURCE_LINES__': '338',
    '__H9_SELECTED_STRICT_STEM__': 'same-symbol-edge-stable-strict-4',
    '__H9_SELECTED_FULL_STEM__': 'same-symbol-edge-stable-public-1',
    '__H9_AUDIT_STEM__': 'same-symbol-edge-stable-audit-1',
    '__H9_AUDIT_LOG_SHA256__': 'c4b5c7f777ec5c09154b2a0fb383b9b7686aa6a9f0370a7ef272b4739fe8fab9',
    '__H9_AUDIT_BUILD_JOBS__': '3626',
    '__H9_AUDIT_DEPENDENCIES__': '75371',
    '__H9_ACTUAL_JOBS__': '6',
    '__H9_SOURCE_JOBS__': '5',
    '__H9_AUDIT_COMMANDS__': '1',
    '__H9_FAILED_JOBS__': '2',
    '__H9_WARNED_SOURCE_ZERO_JOBS__': '1',
    '__H9_REJECTED_PUBLIC_TYPE_JOBS__': '0',
    '__H9_FULL_LOG_SHA256__': 'd3c35861e47b59aa58b4ee16a68b756c8d6cae70037fcf9292677486f79b0050',
    '__H9_FULL_READBACK_PATH__': 'public-readback/same-symbol-edge-stable-full-readback.json',
    '__H9_COMPLETED_TYPE_SHA256__': 'b77d5025ebff2218f5a4214cfe0027434320a0fd1d10868c5f8602c23a684259',
    '__H9_COMPLETED_TYPE_PATH__': 'public-readback/same-symbol-edge-stable-completed_preserves-public-type.txt',
    '__H9_COMPLETED_PRINTED_TYPE_PATH__': 'public-readback/same-symbol-edge-stable-completed_preserves-printed-public-type.txt',
    '__H9_COMPLETED_AXIOMS_JSON__': '["Classical.choice", "Quot.sound", "propext"]',
    '__H9_PUBLIC_TYPE_REVIEW__': 'ROOT_AND_INDEPENDENT_COMPLETE',
}
audit = (HERE / 'same-symbol-edge-stable-audit-1.log').read_bytes()
assert hashlib.sha256(audit).hexdigest() == bindings['__H9_AUDIT_LOG_SHA256__']
assert b'Build completed successfully (3626 jobs).' in audit and b'75371 MicroCFTA theorems' in audit
assert json.loads((HERE / 'same-symbol-edge-stable-audit-1.json').read_text())['exit_code'] == 0
assert (HERE / 'same-symbol-edge-stable-strict-4.log').read_bytes() == b''
review = json.loads((HERE / 'root-full-review.json').read_text())
assert review['source_sha256'] == bindings['__H9_SOURCE_SHA256__']
assert review['complete_public_type_root_review'] == review['independent_complete_public_type_review'] == 'CLEAR'
target = HERE / 'actual-tools-preparation'
target.mkdir()
sources = {name: HERE / 'checkpoint-preparation' / name for name in [
    'verify-preservation.py', 'verify-checkpoint.py', 'commit-proofs.py', 'seal-checkpoint.py',
    'verify-seal.py', 'archive-support.py', 'final-publication.py']}
sources['update-documents.py'] = HERE / 'documents-preparation-v2/update-documents.py'
pins, patches = {}, []
for name, source in sources.items():
    before = source.read_text()
    after = before
    for token, value in bindings.items():
        after = after.replace(token, value)
    assert not re.search(r'__H9_[A-Z_]+__', after), name
    (target / name).write_text(after)
    pins[name] = hashlib.sha256(after.encode()).hexdigest()
    patches.extend(difflib.unified_diff(before.splitlines(True), after.splitlines(True),
        fromfile=str(source.relative_to(HERE)), tofile='actual-tools-preparation/' + name))
(target / 'binding.patch').write_text(''.join(patches))
(target / 'bindings.json').write_text(json.dumps(bindings, indent=2) + '\n')
(target / 'pins.json').write_text(json.dumps(pins, indent=2) + '\n')
print(json.dumps({'status': 'PASS', 'prepared_not_activated': pins}))
