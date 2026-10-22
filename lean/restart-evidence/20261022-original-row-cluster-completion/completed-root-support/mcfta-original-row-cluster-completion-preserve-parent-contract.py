import hashlib
import json
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
previous = root / 'lean/restart-evidence/20261022-original-row-cluster-control'
here = root / 'lean/restart-evidence/20261022-original-row-cluster-completion'
names = ['NEXT-TARGET.md', 'next-cluster-root-review.json']
pins = {}
for name in names:
    source = previous / name
    target = here / ('previous-' + name)
    assert not target.exists()
    data = source.read_bytes()
    target.write_bytes(data)
    assert target.read_bytes() == data
    pins[name] = dict(source=str(source.relative_to(root)),
        snapshot=str(target.relative_to(root)), sha256=hashlib.sha256(data).hexdigest())
output = here / 'previous-contract-pins.json'
assert not output.exists()
output.write_text(json.dumps(pins, indent=2) + '\n')
print(json.dumps({'status': 'PASS', 'files': len(pins)}))
