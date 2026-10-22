import hashlib
import json
import shutil
from pathlib import Path

HERE = Path(__file__).resolve().parent
target = HERE / 'previous-checkpoint-publication'
assert not target.exists()
target.mkdir()
pins = {}
for source in sorted(Path('/tmp').glob('mcfta-same-symbol-edge-control-*')):
    if source.is_file():
        copied = target / source.name
        shutil.copyfile(source, copied)
        assert copied.read_bytes() == source.read_bytes()
        pins[source.name] = hashlib.sha256(copied.read_bytes()).hexdigest()
for name in ['publication.json', 'final-publication-1.json', 'seal-1.json', 'board-readback.json']:
    assert 'mcfta-same-symbol-edge-control-' + name in pins
receipt = json.loads((target / 'mcfta-same-symbol-edge-control-publication.json').read_text())
assert receipt['checkpoint'] == (HERE / 'starting-head.txt').read_text().strip()
registry = HERE / 'archived-components.json'
items = json.loads(registry.read_text())
assert target.name not in items
items[target.name] = pins
registry.write_text(json.dumps(items, indent=2) + '\n')
print(json.dumps({'status': 'PASS', 'files': len(pins), 'component': target.name}))
