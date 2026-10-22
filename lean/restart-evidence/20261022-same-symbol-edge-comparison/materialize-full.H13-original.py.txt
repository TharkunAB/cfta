import hashlib
import json
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
source = HERE / 'full-preparation/prepare-selected-full.py'
pins = json.loads((HERE / 'full-preparation/pins.json').read_text())
assert hashlib.sha256(source.read_bytes()).hexdigest() == pins[source.name]
target = HERE / source.name
assert not target.exists()
target.write_bytes(source.read_bytes())
subprocess.run(['/usr/bin/python3', str(target), 'same-symbol-edge-original-rows-strict-1',
    '9d8af23bc2bbdd97f462a34b4d786d772a55bebf243dd585187b25630ac6440b', '174'], check=True)
