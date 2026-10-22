import hashlib
import json
import shutil
from pathlib import Path

HERE = Path(__file__).resolve().parent
OLD = HERE.parent / '20261022-same-symbol-edge-comparison-domains'
pins = {}
for name in ['NEXT-TARGET.md', 'next-control-root-review.json', 'next-control-authorship-erratum.md']:
    target = HERE / ('previous-' + name)
    assert not target.exists()
    shutil.copyfile(OLD / name, target)
    assert target.read_bytes() == (OLD / name).read_bytes()
    pins[target.name] = hashlib.sha256(target.read_bytes()).hexdigest()
(HERE / 'previous-next-contract-pins.json').write_text(json.dumps(pins, indent=2) + '\n')
print(json.dumps({'status': 'PASS', 'files': pins, 'proof_jobs': 0}))
