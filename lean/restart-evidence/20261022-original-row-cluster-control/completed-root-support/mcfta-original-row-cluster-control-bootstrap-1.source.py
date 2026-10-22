import ast
import difflib
import hashlib
import json
from pathlib import Path

ROOT = Path('/home/tritlo/Code/mcfta')
old = ROOT / 'lean/restart-evidence/20261022-same-symbol-edge-comparison-domains'
here = ROOT / 'lean/restart-evidence/20261022-original-row-cluster-control'
assert not here.exists()
here.mkdir()
names = ['root-driver.py', 'root-capped-worker.py', 'root-run-check.py',
         'archive-extra.py', 'archive-packages.py', 'start.py']
pins = {}
for name in names:
    before = (old / name).read_text()
    after = before
    if name == 'root-driver.py':
        after = after.replace('20261022-same-symbol-edge-comparison-domains', '20261022-original-row-cluster-control')
    if name == 'start.py':
        after = after.replace('e8a0066c6088d87cc0b0ea9085a07ba2ff44913c', '4f7a7e064f17a66367618dc2bc360f0755503b1a')
        after = after.replace('backup-same-symbol-edge-comparison-domains-20261022-0500', 'backup-original-row-cluster-control-20261022-0548')
        after = after.replace('/tmp/mcfta-same-symbol-edge-comparison-local-publication.json',
                              '/tmp/mcfta-same-symbol-edge-comparison-domains-local-publication.json')
    ast.parse(after)
    (here / name).write_text(after)
    if before != after:
        (here / (name + '.H15-original.txt')).write_text(before)
        (here / (name + '.patch')).write_text(''.join(difflib.unified_diff(
            before.splitlines(True), after.splitlines(True), fromfile='H15/' + name, tofile='H16/' + name)))
    pins[name] = hashlib.sha256(after.encode()).hexdigest()
driver = Path('/tmp/mcfta-original-row-cluster-control-driver.py')
assert not driver.exists()
driver.write_bytes((here / 'root-driver.py').read_bytes())
(here / 'bootstrap-pins.json').write_text(json.dumps(pins, indent=2) + '\n')
print(json.dumps({'status': 'PREPARED', 'helpers': pins, 'proof_jobs': 0}))
