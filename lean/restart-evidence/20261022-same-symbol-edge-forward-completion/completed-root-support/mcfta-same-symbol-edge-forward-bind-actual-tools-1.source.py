import difflib
import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
bindings = {
    '__H8_SOURCE_SHA256__': 'c1b7480244632c2cc0454051f0dc7f63649d9ed4cf3c2548edf615ff8647aafd',
    '__H8_SOURCE_LINES__': '216',
    '__H8_SELECTED_STRICT_STEM__': 'same-symbol-edge-forward-strict-3',
    '__H8_SELECTED_FULL_STEM__': 'same-symbol-edge-forward-public-1',
    '__H8_AUDIT_STEM__': 'same-symbol-edge-forward-audit-1',
    '__H8_AUDIT_LOG_SHA256__': '035b57c4aa2f1d23b5e158d06e5672c97673780ee8ba70e65e1809bfe8828a56',
    '__H8_AUDIT_BUILD_JOBS__': '3625',
    '__H8_AUDIT_DEPENDENCIES__': '75347',
    '__H8_ACTUAL_JOBS__': '5',
    '__H8_SOURCE_JOBS__': '4',
    '__H8_AUDIT_JOB_COUNT__': '1',
    '__H8_FAILED_JOBS__': '2',
    '__H8_WARNED_SOURCE_EXIT_ZERO_JOBS__': '0',
    '__H8_REJECTED_PUBLIC_TYPE_JOBS__': '0',
    '__H8_FULL_LOG_SHA256__': '9956f259c447276fce689f81d80f0fa535c4fed1f2e9cd1753a0d535ea8ae2dc',
    '__H8_FULL_READBACK_PATH__': 'public-readback/same-symbol-edge-forward-full-readback.json',
    '__H8_CHECKED_TYPE_PATH__': 'public-readback/same-symbol-edge-forward-both_miss_complete-public-type.txt',
    '__H8_PRINTED_TYPE_PATH__': 'public-readback/same-symbol-edge-forward-both_miss_complete-printed-public-type.txt',
    '__H8_TYPE_SHA256__': '1ffb0db3a32326db3cb9354b0870fc5bce8b9b7e561bbd9f90f75e3fe293ab00',
    '__H8_PROOF_REPORT_PATH__': 'proof-evidence-normal.json',
}
audit = (HERE / 'same-symbol-edge-forward-audit-1.log').read_bytes()
assert hashlib.sha256(audit).hexdigest() == bindings['__H8_AUDIT_LOG_SHA256__']
assert b'Build completed successfully (3625 jobs).' in audit and b'75347 MicroCFTA theorems' in audit
assert json.loads((HERE / 'same-symbol-edge-forward-audit-1.json').read_text())['exit_code'] == 0
target = HERE / 'actual-tools-preparation'
target.mkdir()
sources = {name: HERE / 'checkpoint-preparation-v2' / name for name in [
    'verify-preservation.py', 'verify-checkpoint.py', 'commit-proofs.py', 'seal-checkpoint.py',
    'verify-seal.py', 'archive-support.py', 'final-publication.py']}
sources['update-documents.py'] = HERE / 'documents-preparation/update-documents.py'
pins, patches = {}, []
for name, source in sources.items():
    before = source.read_text()
    after = before
    for token, value in bindings.items():
        after = after.replace(token, value)
    assert not re.search(r'__H8_[A-Z_]+__', after), name
    (target / name).write_text(after)
    pins[name] = hashlib.sha256(after.encode()).hexdigest()
    patches.extend(difflib.unified_diff(before.splitlines(True), after.splitlines(True),
        fromfile=str(source.relative_to(HERE)), tofile='actual-tools-preparation/' + name))
(target / 'binding.patch').write_text(''.join(patches))
(target / 'bindings.json').write_text(json.dumps(bindings, indent=2) + '\n')
(target / 'pins.json').write_text(json.dumps(pins, indent=2) + '\n')
print(json.dumps({'status': 'PASS', 'prepared_not_activated': pins}))
