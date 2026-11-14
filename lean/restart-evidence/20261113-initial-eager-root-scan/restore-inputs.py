from pathlib import Path
import hashlib
import json
import subprocess
import sys

root = Path.cwd()
target = Path(sys.argv[1]).resolve()
packet = Path(__file__).resolve().parent
manifest = json.loads((packet / 'manifest.json').read_text())
previous = manifest['previous_checkpoint']
new = manifest['public_source']['path']
pins = {}
for path in sorted((root / 'lean/MicroCFTA').glob('*.lean')):
    name = str(path.relative_to(root))
    if name == new:
        continue
    data = subprocess.check_output(['git', 'show', previous + ':' + name], cwd=root) if name == 'lean/MicroCFTA/Audit.lean' else path.read_bytes()
    pins[name] = hashlib.sha256(data).hexdigest()
data = (json.dumps(pins, indent=2) + '\n').encode()
expected = next(x['sha256'] for x in manifest['regenerable_inputs'] if x['name'] == 'baseline-live-source-pins.json')
assert hashlib.sha256(data).hexdigest() == expected
target.mkdir(parents=True, exist_ok=True)
(target / 'baseline-live-source-pins.json').write_bytes(data)
print('Restored the exact historical baseline pins.')
