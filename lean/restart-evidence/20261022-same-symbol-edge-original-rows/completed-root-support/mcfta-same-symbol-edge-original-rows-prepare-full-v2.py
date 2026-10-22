import ast
import difflib
import hashlib
import json
import shutil
from pathlib import Path

OLD = Path('/tmp/mcfta-same-symbol-edge-original-rows-full-preparation')
HERE = Path('/tmp/mcfta-same-symbol-edge-original-rows-full-preparation-v2')
assert not HERE.exists()
shutil.copytree(OLD, HERE)
before = (HERE / 'prepare-selected-full.py').read_bytes()
old = 'assert source.startswith(context + header)\n'
new = ('assert source.startswith(context)\n'
       'assert source.count(header) == 1\n'
       'assert source.index(header) >= len(context)\n')
assert before.decode().count(old) == 1
after = before.decode().replace(old, new)
ast.parse(after)
(HERE / 'prepare-selected-full.v1.py.txt').write_bytes(before)
(HERE / 'prepare-selected-full.py').write_text(after)
(HERE / 'prepare-selected-full.v1-to-v2.patch').write_text(''.join(difflib.unified_diff(
    before.decode().splitlines(keepends=True), after.splitlines(keepends=True),
    fromfile='V1/prepare-selected-full.py', tofile='V2/prepare-selected-full.py')))
for name in ['pins.json', 'status.json']:
    (HERE / ('v1-' + name)).write_bytes((HERE / name).read_bytes())
(HERE / 'status.json').write_text(json.dumps({'status': 'FROZEN_SOURCE_ONLY_V2',
    'prepared_scripts_executed': 0, 'new_proof_jobs': 0,
    'reason': 'Keep exact context and unique exact public header with private helpers between them.',
    'reader_unchanged_from_v1': True, 'proof_source_unchanged': True}, indent=2) + '\n')
(HERE / 'pins.json').write_text(json.dumps({
    str(p.relative_to(HERE)): hashlib.sha256(p.read_bytes()).hexdigest()
    for p in sorted(HERE.rglob('*')) if p.is_file() and p.name != 'pins.json'
}, indent=2) + '\n')
print(json.dumps({'status': 'PASS', 'prepared': str(HERE), 'new_proof_jobs': 0}))
