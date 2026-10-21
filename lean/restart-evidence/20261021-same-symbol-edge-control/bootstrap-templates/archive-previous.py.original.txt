import hashlib
import json
import shutil
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
target = HERE / 'previous-checkpoint-publication'
assert not target.exists()
target.mkdir()
pins = {}
for source in sorted(Path('/tmp').glob('mcfta-finite-warm-calls-*')):
    if source.is_file():
        copied = target / source.name
        shutil.copyfile(source, copied)
        assert copied.read_bytes() == source.read_bytes()
        pins[source.name] = hashlib.sha256(copied.read_bytes()).hexdigest()
assert 'mcfta-finite-warm-calls-publication.json' in pins
assert 'mcfta-finite-warm-calls-final-publication-1.json' in pins
assert 'mcfta-finite-warm-calls-seal-1.json' in pins
receipt = json.loads((target / 'mcfta-finite-warm-calls-publication.json').read_text())
assert receipt['checkpoint'] == (HERE / 'starting-head.txt').read_text().strip()
registry = HERE / 'archived-components.json'
assert not registry.exists()
registry.write_text(json.dumps({'previous-checkpoint-publication': pins}, indent=2) + '\n')
print(json.dumps({'status': 'PASS', 'files': len(pins), 'component': target.name}))
