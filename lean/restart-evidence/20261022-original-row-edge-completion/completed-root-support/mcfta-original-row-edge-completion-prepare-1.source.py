import difflib
import hashlib
import json
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
old = root / 'lean/restart-evidence/20261022-same-symbol-edge-ready'
new = root / 'lean/restart-evidence/20261022-original-row-edge-completion'
assert not new.exists()
new.mkdir()
history = new / 'bootstrap-predecessors'
history.mkdir()
pins, patches = {}, []
for name in ['root-capped-worker.py', 'root-run-check.py', 'archive-extra.py', 'start.py']:
    before = (old / name).read_text()
    after = before
    if name == 'start.py':
        for first, second in [
            ('f985c09f5b18b740082799e15abc4736b3cbf880', '47c597a8e39cb82aa158a9fca104ed41b24849ef'),
            ('codex/backup-same-symbol-edge-ready-20261022-0214', 'codex/backup-original-row-edge-completion-20261022-0246'),
            ('/tmp/mcfta-same-symbol-edge-stable-publication.json', '/tmp/mcfta-same-symbol-edge-ready-publication.json'),
        ]:
            assert after.count(first) == 1
            after = after.replace(first, second)
    (history / (name + '.txt')).write_text(before)
    (new / name).write_text(after)
    pins[name] = hashlib.sha256(after.encode()).hexdigest()
    patches.extend(difflib.unified_diff(before.splitlines(True), after.splitlines(True),
        fromfile='H10/' + name, tofile='H11/' + name))
driver = Path('/tmp/mcfta-original-row-edge-completion-driver.py')
assert not driver.exists()
before = Path('/tmp/mcfta-same-symbol-edge-ready-driver.py').read_text()
assert before.count('20261022-same-symbol-edge-ready') == 1
after = before.replace('20261022-same-symbol-edge-ready', '20261022-original-row-edge-completion')
driver.write_text(after)
(history / 'driver.py.txt').write_text(before)
(new / 'root-driver.py').write_text(after)
pins['root-driver.py'] = hashlib.sha256(after.encode()).hexdigest()
patches.extend(difflib.unified_diff(before.splitlines(True), after.splitlines(True), fromfile='H10/driver.py', tofile='H11/driver.py'))
(new / 'bootstrap.patch').write_text(''.join(patches))
(new / 'bootstrap-pins.json').write_text(json.dumps(pins, indent=2) + '\n')
(new / 'prepare-checkpoint.py').write_bytes(Path(__file__).read_bytes())
print(json.dumps({'status': 'PASS', 'prepared': pins, 'start_not_executed': True}))
