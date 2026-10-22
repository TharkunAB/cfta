import ast
import difflib
import hashlib
import json
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
old = root / 'lean/restart-evidence/20261022-original-row-cluster-completion'
here = root / 'lean/restart-evidence/20261022-original-row-physical-meaning'
assert not here.exists()
here.mkdir()
pins = {}
for name in ['root-driver.py', 'root-capped-worker.py', 'root-run-check.py', 'archive-extra.py', 'archive-packages.py', 'start.py']:
    before = (old / name).read_text()
    after = before
    if name == 'root-driver.py':
        after = after.replace('20261022-original-row-cluster-completion', '20261022-original-row-physical-meaning')
    if name == 'start.py':
        after = after.replace('562120d456ea5836dc0f3cc718dafd25323521c3', '4fffdcea9e49afb54ff4c3218347a830df4cc39d')
        after = after.replace('backup-original-row-cluster-completion-20261022-0636', 'backup-original-row-physical-meaning-20261022-0752')
        after = after.replace('/tmp/mcfta-original-row-cluster-control-local-publication.json', '/tmp/mcfta-original-row-cluster-completion-local-publication.json')
    ast.parse(after)
    (here / name).write_text(after)
    if before != after:
        (here / (name + '.H17-original.txt')).write_text(before)
        (here / (name + '.patch')).write_text(''.join(difflib.unified_diff(
            before.splitlines(True), after.splitlines(True), fromfile='H17/' + name, tofile='H18/' + name)))
    pins[name] = hashlib.sha256(after.encode()).hexdigest()
driver = Path('/tmp/mcfta-original-row-physical-meaning-driver.py')
assert not driver.exists()
driver.write_bytes((here / 'root-driver.py').read_bytes())
(here / 'bootstrap-pins.json').write_text(json.dumps(pins, indent=2) + '\n')
print(json.dumps(dict(status='PREPARED', helpers=6, proof_jobs=0)))
