import ast
import difflib
import hashlib
import json
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
old = root / 'lean/restart-evidence/20261022-original-row-physical-meaning'
here = root / 'lean/restart-evidence/20261022-original-row-deletion-soundness'
assert not here.exists()
here.mkdir()
pins = {}
for name in ['root-driver.py', 'root-capped-worker.py', 'root-run-check.py', 'archive-extra.py', 'archive-packages.py', 'start.py']:
    before = (old / name).read_text()
    after = before
    if name == 'root-driver.py':
        after = after.replace('20261022-original-row-physical-meaning', '20261022-original-row-deletion-soundness')
    if name == 'start.py':
        after = after.replace('4fffdcea9e49afb54ff4c3218347a830df4cc39d', 'a8223aafa4ef99da5570f2013aadc14af99076b3')
        after = after.replace('backup-original-row-physical-meaning-20261022-0752', 'backup-original-row-deletion-soundness-20261022-0840')
        after = after.replace('/tmp/mcfta-original-row-cluster-completion-local-publication.json', '/tmp/mcfta-original-row-physical-meaning-local-publication.json')
    ast.parse(after)
    (here / name).write_text(after)
    if before != after:
        (here / (name + '.H18-original.txt')).write_text(before)
        (here / (name + '.patch')).write_text(''.join(difflib.unified_diff(
            before.splitlines(True), after.splitlines(True), fromfile='H18/' + name, tofile='H19/' + name)))
    pins[name] = hashlib.sha256(after.encode()).hexdigest()
driver = Path('/tmp/mcfta-original-row-deletion-soundness-driver.py')
assert not driver.exists()
driver.write_bytes((here / 'root-driver.py').read_bytes())
(here / 'bootstrap-pins.json').write_text(json.dumps(pins, indent=2) + '\n')
print(json.dumps(dict(status='PREPARED', helpers=6, proof_jobs=0)))
