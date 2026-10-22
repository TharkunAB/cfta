import ast
import difflib
import hashlib
import json
from pathlib import Path

ROOT = Path('/home/tritlo/Code/mcfta')
PREVIOUS = ROOT / 'lean/restart-evidence/20261022-same-symbol-edge-comparison'
HERE = ROOT / 'lean/restart-evidence/20261022-same-symbol-edge-comparison-domains'
assert not HERE.exists()
HERE.mkdir()
archive = HERE / 'bootstrap-predecessors'
archive.mkdir()
pins = {}
names = ['root-run-check.py', 'root-capped-worker.py', 'archive-extra.py',
         'archive-packages.py', 'start.py', 'root-driver.py']
for name in names:
    before = (PREVIOUS / name).read_text()
    after = before
    if name == 'start.py':
        changes = {
            '1d5a07b762950272e53c9bd2d5f478d7be39dfad': 'e8a0066c6088d87cc0b0ea9085a07ba2ff44913c',
            'codex/backup-same-symbol-edge-comparison-20261022-0424':
                'codex/backup-same-symbol-edge-comparison-domains-20261022-0500',
            '/tmp/mcfta-same-symbol-edge-original-rows-local-publication.json':
                '/tmp/mcfta-same-symbol-edge-comparison-local-publication.json',
        }
        for old, new in changes.items():
            assert after.count(old) == 1
            after = after.replace(old, new)
    if name == 'root-driver.py':
        old = 'lean/restart-evidence/20261022-same-symbol-edge-comparison'
        assert after.count(old) == 1
        after = after.replace(old, old + '-domains')
    ast.parse(after)
    (archive / (name + '.txt')).write_text(before)
    (archive / (name + '.patch')).write_text(''.join(difflib.unified_diff(
        before.splitlines(True), after.splitlines(True), fromfile='H14/' + name, tofile='H15/' + name)))
    (HERE / name).write_text(after)
    pins[name] = {'before_sha256': hashlib.sha256(before.encode()).hexdigest(),
                  'after_sha256': hashlib.sha256(after.encode()).hexdigest()}
(archive / 'pins.json').write_text(json.dumps(pins, indent=2) + '\n')
driver = Path('/tmp/mcfta-same-symbol-edge-comparison-domains-driver.py')
assert not driver.exists()
driver.write_bytes((HERE / 'root-driver.py').read_bytes())
print(json.dumps({'status': 'BOOTSTRAPPED', 'helpers': len(names), 'proof_jobs': 0}))
