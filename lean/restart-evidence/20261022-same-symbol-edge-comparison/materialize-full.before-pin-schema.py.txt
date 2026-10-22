import difflib
import hashlib
import json
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
source = HERE / 'full-preparation/prepare-selected-full.py'
pins = json.loads((HERE / 'full-preparation/pins.json').read_text())
assert hashlib.sha256(source.read_bytes()).hexdigest() == pins[source.name]
assert (HERE / 'full-reader-audit/review.md').is_file()
old = (HERE.parent / '20261022-same-symbol-edge-original-rows/materialize-full.py').read_bytes()
(HERE / 'materialize-full.H13-original.py.txt').write_bytes(old)
(HERE / 'materialize-full.patch').write_text(''.join(difflib.unified_diff(
    old.decode().splitlines(keepends=True), Path(__file__).read_text().splitlines(keepends=True),
    fromfile='H13-materialize-full', tofile='H14-materialize-full')))
target = HERE / source.name
assert not target.exists()
target.write_bytes(source.read_bytes())
subprocess.run(['/usr/bin/python3', str(target), 'same-symbol-edge-comparison-strict-1',
    '02d01576ce9e7188342835138452a5163b150e28c264c01782137848e1a1c560', '112'], check=True)
