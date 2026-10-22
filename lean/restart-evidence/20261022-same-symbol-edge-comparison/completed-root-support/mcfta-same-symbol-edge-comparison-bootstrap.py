import ast
import difflib
import hashlib
import json
from pathlib import Path

ROOT = Path('/home/tritlo/Code/mcfta')
OLD = ROOT / 'lean/restart-evidence/20261022-same-symbol-edge-original-rows'
HERE = ROOT / 'lean/restart-evidence/20261022-same-symbol-edge-comparison'
START = '1d5a07b762950272e53c9bd2d5f478d7be39dfad'
assert not HERE.exists()
HERE.mkdir()
previous = HERE / 'bootstrap-predecessors'
previous.mkdir()
patches = {}

def save(name, data, predecessor):
    ast.parse(data)
    (previous / (name + '.txt')).write_bytes(predecessor)
    (HERE / name).write_text(data)
    patches[name] = ''.join(difflib.unified_diff(
        predecessor.decode().splitlines(keepends=True), data.splitlines(keepends=True),
        fromfile='H13/' + name, tofile='H14/' + name))

for name in ['root-run-check.py', 'root-capped-worker.py', 'archive-extra.py']:
    data = (OLD / name).read_bytes()
    save(name, data.decode(), data)
before = (OLD / 'start.py').read_bytes()
data = before.decode()
for old, new in [
    ('c49dd66acf3beecbead06219f10f125a43b3925d', START),
    ('codex/backup-same-symbol-edge-original-rows-20261022-0356',
     'codex/backup-same-symbol-edge-comparison-20261022-0424'),
    ('/tmp/mcfta-direct-edge-word-ranges-local-publication.json',
     '/tmp/mcfta-same-symbol-edge-original-rows-local-publication.json'),
]:
    assert data.count(old) == 1, old
    data = data.replace(old, new)
save('start.py', data, before)
driver_before = Path('/tmp/mcfta-same-symbol-edge-original-rows-driver.py').read_bytes()
driver = driver_before.decode()
old_path = 'lean/restart-evidence/20261022-same-symbol-edge-original-rows'
assert driver.count(old_path) == 1
driver = driver.replace(old_path, str(HERE.relative_to(ROOT)))
ast.parse(driver)
(previous / 'root-driver.py.txt').write_bytes(driver_before)
(HERE / 'root-driver.py').write_text(driver)
Path('/tmp/mcfta-same-symbol-edge-comparison-driver.py').write_text(driver)
patches['root-driver.py'] = ''.join(difflib.unified_diff(
    driver_before.decode().splitlines(keepends=True), driver.splitlines(keepends=True),
    fromfile='H13/root-driver.py', tofile='H14/root-driver.py'))
for name, patch in patches.items():
    (previous / (name + '.patch')).write_text(patch)
(previous / 'pins.json').write_text(json.dumps({
    str(p.relative_to(previous)): hashlib.sha256(p.read_bytes()).hexdigest()
    for p in sorted(previous.iterdir()) if p.is_file()
}, indent=2) + '\n')
print(json.dumps({'status': 'PASS', 'starting_commit': START,
                  'bootstrap_files': list(patches), 'proof_jobs': 0}))
