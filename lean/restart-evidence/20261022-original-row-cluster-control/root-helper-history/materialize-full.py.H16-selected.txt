import difflib
import hashlib
import json
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
old = (HERE / 'full-preparation/prepare-selected-full.py').read_bytes()
target = HERE / 'prepare-selected-full.py'
actual = target.read_bytes()
expected = old.replace(b"'full-preparation/proposed-signature.lean.txt'", b"'source-repair-v2/proposed-signature.lean.txt'")
expected = expected.replace(b'assert not snapshot.exists() and not printer.exists()\n',
    b"assert not snapshot.exists() and not printer.exists() and not (HERE / 'actual-header.lean.txt').exists()\n")
assert actual == expected
assert hashlib.sha256(actual).hexdigest() == '7f79491691444a0c7b9a95c69f2b6874136892fc7e3ab5ed1de688f3245eb3c1'
review = (HERE / 'source-repair-audit-v2/review.md').read_bytes()
assert hashlib.sha256(review).hexdigest() == sys.argv[1]
pins = json.loads((HERE / 'full-preparation/pins.json').read_text())['files']
for name in ['check-full-public.py', 'diagnostic-tail.lean.txt', 'prepare-selected-full.py']:
    assert hashlib.sha256((HERE / 'full-preparation' / name).read_bytes()).hexdigest() == pins[name]['sha256']
(HERE / 'prepare-selected-full.H16-v1.py.txt').write_bytes(old)
(HERE / 'prepare-selected-full.patch').write_text(''.join(difflib.unified_diff(
    old.decode().splitlines(keepends=True), actual.decode().splitlines(keepends=True),
    fromfile='H16-v1-materializer', tofile='H16-v2-materializer')))
subprocess.run(['/usr/bin/python3', str(target), 'original-row-cluster-control-strict-2',
    '37bcce3d4b04310f6e3c1e394e27a875baf98547f4078d1b3be7252c47d0a5f7', '129'], check=True)
gate = dict(status='ROOT_APPROVED_FOR_ONE_FULL_PUBLIC_CHECK',
    source_sha256='37bcce3d4b04310f6e3c1e394e27a875baf98547f4078d1b3be7252c47d0a5f7',
    authorized_job='original-row-cluster-control-public-1', source_lines=129,
    root_read_complete_reader_materializer_tail=True,
    complete_independent_tool_review=True, independent_repair_review_sha256=sys.argv[1],
    exact_after_module_diagnostic_tail=True, default_declaration_limits=True)
assert not (HERE / 'full-materialization-gate.json').exists()
(HERE / 'full-materialization-gate.json').write_text(json.dumps(gate, indent=2) + '\n')
print(json.dumps(gate))
