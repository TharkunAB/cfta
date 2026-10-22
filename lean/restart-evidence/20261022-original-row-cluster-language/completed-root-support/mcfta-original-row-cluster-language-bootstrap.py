import ast
import difflib
import hashlib
import json
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
old = root / 'lean/restart-evidence/20261022-original-row-deletion-soundness'
here = root / 'lean/restart-evidence/20261022-original-row-cluster-language'
assert not here.exists()
here.mkdir()
pins = {}
for name in ['root-driver.py', 'root-capped-worker.py', 'root-run-check.py', 'archive-extra.py', 'archive-packages.py', 'start.py']:
    before = (old / name).read_text()
    after = before
    if name == 'root-driver.py':
        after = after.replace('20261022-original-row-deletion-soundness', '20261022-original-row-cluster-language')
    if name == 'start.py':
        after = after.replace('a8223aafa4ef99da5570f2013aadc14af99076b3', '21dbf7da7ec880f6d9673213934f764e6fda7999')
        after = after.replace('backup-original-row-deletion-soundness-20261022-0840', 'backup-original-row-cluster-language-20261022-2144')
        after = after.replace('/tmp/mcfta-original-row-physical-meaning-local-publication.json', '/tmp/mcfta-original-row-deletion-soundness-local-publication.json')
    ast.parse(after)
    (here / name).write_text(after)
    if before != after:
        (here / (name + '.H19-original.txt')).write_text(before)
        (here / (name + '.patch')).write_text(''.join(difflib.unified_diff(
            before.splitlines(True), after.splitlines(True), fromfile='H19/' + name, tofile='H20/' + name)))
    pins[name] = hashlib.sha256(after.encode()).hexdigest()
driver = Path('/tmp/mcfta-original-row-cluster-language-driver.py')
assert not driver.exists()
driver.write_bytes((here / 'root-driver.py').read_bytes())
(here / 'bootstrap-pins.json').write_text(json.dumps(pins, indent=2) + '\n')
print(json.dumps(dict(status='PREPARED', helpers=6, proof_jobs=0)))
