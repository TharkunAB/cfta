import difflib
import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
bindings = {
    '__H11_SOURCE_SHA__': '646095a73f7927c820752de30b47275abf879783760d54f8c31611b93e35feb0',
    '__H11_SOURCE_LINES__': '81',
    '__H11_SELECTED_STRICT__': 'original-row-edge-completion-strict-1',
    '__H11_SELECTED_FULL__': 'original-row-edge-completion-public-1',
    '__H11_AUDIT_STEM__': 'original-row-edge-completion-audit-1',
    '__H11_AUDIT_SHA__': '6ea3ec3d0e64000cdca8234d09aa1623703b5708547a3dec1d669454a6589e2f',
    '__H11_AUDIT_BUILD_JOBS__': '3628',
    '__H11_AUDIT_DEPENDENCIES__': '75379',
    '__H11_ACTUAL_JOBS__': '3',
    '__H11_SOURCE_JOBS__': '2',
    '__H11_AUDIT_JOBS__': '1',
    '__H11_FAILED_JOBS__': '0',
    '__H11_WARNED_SOURCE_EXIT_ZERO_JOBS__': '0',
    '__H11_REJECTED_PUBLIC_TYPE_JOBS__': '0',
    '__H11_FULL_RAW_SHA__': 'da9201525fc5e62bc3828e41166802a81ac2d0d95412c532a23fde7688cd57cb',
    '__H11_TYPE_SHA__': '8d04a75592757126c66ee07e63abecced1d9fa722facd4b4aef74e67d63f8d01',
    '__H11_ACTUAL_AXIOMS_JSON__': '["Classical.choice", "Quot.sound", "propext"]',
    '__H11_TYPE_REVIEW_STATUS__': 'ROOT_AND_INDEPENDENT_COMPLETE',
}
audit = (HERE / 'original-row-edge-completion-audit-1.log').read_bytes()
assert hashlib.sha256(audit).hexdigest() == bindings['__H11_AUDIT_SHA__']
assert b'Build completed successfully (3628 jobs).' in audit and b'75379 MicroCFTA theorems' in audit
assert json.loads((HERE / 'original-row-edge-completion-audit-1.json').read_text())['exit_code'] == 0
assert (HERE / 'original-row-edge-completion-strict-1.log').read_bytes() == b''
review = json.loads((HERE / 'root-full-review.json').read_text())
assert review['source_sha256'] == bindings['__H11_SOURCE_SHA__']
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
    assert not re.search(r'__H11_[A-Z_]+__', after), name
    (target / name).write_text(after)
    pins[name] = hashlib.sha256(after.encode()).hexdigest()
    patches.extend(difflib.unified_diff(before.splitlines(True), after.splitlines(True),
        fromfile=str(source.relative_to(HERE)), tofile='actual-tools-preparation/' + name))
(target / 'binding.patch').write_text(''.join(patches))
(target / 'bindings.json').write_text(json.dumps(bindings, indent=2) + '\n')
(target / 'pins.json').write_text(json.dumps(pins, indent=2) + '\n')
print(json.dumps({'status': 'PASS', 'prepared_not_activated': pins}))
