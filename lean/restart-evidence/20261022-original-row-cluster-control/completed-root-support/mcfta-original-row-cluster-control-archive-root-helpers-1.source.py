import ast
import difflib
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
OLD = HERE.parent / '20261022-same-symbol-edge-comparison-domains'
target = HERE / 'root-helper-history'
assert not target.exists()
target.mkdir()
pins = {}
for name in ['materialize-full.py', 'accept-full-review.py', 'install-source.py',
    'bind-actual-evidence.py', 'activate-proof-tools.py', 'run-proof-evidence.py', 'finalize-review-packet.py']:
    before, after = (OLD / name).read_bytes(), (HERE / name).read_bytes()
    ast.parse(after.decode())
    assert before != after
    (target / (name + '.H15-original.txt')).write_bytes(before)
    (target / (name + '.H16-selected.txt')).write_bytes(after)
    (target / (name + '.patch')).write_text(''.join(difflib.unified_diff(
        before.decode().splitlines(keepends=True), after.decode().splitlines(keepends=True),
        fromfile='H15/' + name, tofile='H16/' + name)))
for path in target.iterdir():
    pins[path.name] = hashlib.sha256(path.read_bytes()).hexdigest()
(target / 'pins.json').write_text(json.dumps(pins, indent=2) + '\n')
print(json.dumps({'status': 'SOURCE_HISTORY_PRESERVED', 'files': len(pins), 'executed_helpers': 0}))
