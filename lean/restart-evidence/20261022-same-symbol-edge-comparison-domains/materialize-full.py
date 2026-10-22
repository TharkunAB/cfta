import difflib
import hashlib
import json
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
source = HERE / 'full-preparation/prepare-selected-full.py'
pins = json.loads((HERE / 'full-preparation/pins.json').read_text())
assert hashlib.sha256(source.read_bytes()).hexdigest() == pins['files'][source.name]['sha256']
assert (HERE / 'full-reader-audit/review.md').is_file()
old = (HERE.parent / '20261022-same-symbol-edge-comparison/materialize-full.py').read_bytes()
(HERE / 'materialize-full.H14-original.py.txt').write_bytes(old)
(HERE / 'materialize-full.patch').write_text(''.join(difflib.unified_diff(
    old.decode().splitlines(keepends=True), Path(__file__).read_text().splitlines(keepends=True),
    fromfile='H14-materialize-full', tofile='H15-materialize-full')))
target = HERE / source.name
assert not target.exists()
target.write_bytes(source.read_bytes())
subprocess.run(['/usr/bin/python3', str(target), 'same-symbol-edge-comparison-domains-strict-1',
    '8ae94566570cf99ec3eb61ec991d36a1df196c5b9c2bc2fca4aeb88fd6305e15', '189'], check=True)
