import ast
import difflib
import hashlib
import json
from pathlib import Path

ROOT = Path('/home/tritlo/Code/mcfta')
old = ROOT / 'lean/restart-evidence/20261022-original-row-cluster-control'
here = ROOT / 'lean/restart-evidence/20261022-original-row-cluster-completion'
assert not here.exists()
here.mkdir()
names = ['root-driver.py', 'root-capped-worker.py', 'root-run-check.py',
         'archive-extra.py', 'archive-packages.py', 'start.py']
pins = {}
for name in names:
    before = (old / name).read_text()
    after = before
    if name == 'root-driver.py':
        after = after.replace('20261022-original-row-cluster-control', '20261022-original-row-cluster-completion')
    if name == 'start.py':
        after = after.replace('4f7a7e064f17a66367618dc2bc360f0755503b1a', '562120d456ea5836dc0f3cc718dafd25323521c3')
        after = after.replace('backup-original-row-cluster-control-20261022-0548', 'backup-original-row-cluster-completion-20261022-0636')
        after = after.replace('/tmp/mcfta-same-symbol-edge-comparison-domains-local-publication.json',
                              '/tmp/mcfta-original-row-cluster-control-local-publication.json')
    ast.parse(after)
    (here / name).write_text(after)
    if before != after:
        (here / (name + '.H16-original.txt')).write_text(before)
        (here / (name + '.patch')).write_text(''.join(difflib.unified_diff(
            before.splitlines(True), after.splitlines(True), fromfile='H16/' + name, tofile='H17/' + name)))
    pins[name] = hashlib.sha256(after.encode()).hexdigest()
driver = Path('/tmp/mcfta-original-row-cluster-completion-driver.py')
assert not driver.exists()
driver.write_bytes((here / 'root-driver.py').read_bytes())
(here / 'bootstrap-pins.json').write_text(json.dumps(pins, indent=2) + '\n')
print(json.dumps({'status': 'PREPARED', 'helpers': pins, 'proof_jobs': 0}))
