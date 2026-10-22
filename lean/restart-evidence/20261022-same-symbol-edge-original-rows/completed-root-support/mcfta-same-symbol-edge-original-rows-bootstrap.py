import ast
import difflib
import hashlib
import json
from pathlib import Path

ROOT = Path('/home/tritlo/Code/mcfta')
OLD = ROOT / 'lean/restart-evidence/20261022-direct-edge-word-ranges'
HERE = ROOT / 'lean/restart-evidence/20261022-same-symbol-edge-original-rows'
START = 'c49dd66acf3beecbead06219f10f125a43b3925d'
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
        fromfile='H12/' + name, tofile='H13/' + name))

for name in ['root-run-check.py', 'root-capped-worker.py', 'archive-extra.py']:
    data = (OLD / name).read_bytes()
    save(name, data.decode(), data)
name = 'start.py'
before = (OLD / name).read_bytes()
data = before.decode()
for old, new in [
    ('108bc09e803b90b5e2e790c796d7ffd3c1d2f39f', START),
    ('codex/backup-direct-edge-word-ranges-20261022-0319',
     'codex/backup-same-symbol-edge-original-rows-20261022-0356'),
    ('/tmp/mcfta-original-row-edge-completion-local-publication.json',
     '/tmp/mcfta-direct-edge-word-ranges-local-publication.json'),
]:
    assert data.count(old) == 1, old
    data = data.replace(old, new)
save(name, data, before)

driver_before = Path('/tmp/mcfta-direct-edge-word-ranges-driver.py').read_bytes()
driver = driver_before.decode()
old_path = 'lean/restart-evidence/20261022-direct-edge-word-ranges'
assert driver.count(old_path) == 1
driver = driver.replace(old_path, str(HERE.relative_to(ROOT)))
ast.parse(driver)
(previous / 'root-driver.py.txt').write_bytes(driver_before)
(HERE / 'root-driver.py').write_text(driver)
Path('/tmp/mcfta-same-symbol-edge-original-rows-driver.py').write_text(driver)
patches['root-driver.py'] = ''.join(difflib.unified_diff(
    driver_before.decode().splitlines(keepends=True), driver.splitlines(keepends=True),
    fromfile='H12/root-driver.py', tofile='H13/root-driver.py'))
for name, patch in patches.items():
    (previous / (name + '.patch')).write_text(patch)
(previous / 'pins.json').write_text(json.dumps({
    str(p.relative_to(previous)): hashlib.sha256(p.read_bytes()).hexdigest()
    for p in sorted(previous.iterdir()) if p.is_file()
}, indent=2) + '\n')
print(json.dumps({'status': 'PASS', 'starting_commit': START,
                  'bootstrap_files': list(patches), 'proof_jobs': 0}))
