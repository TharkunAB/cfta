import hashlib
import json
import shutil
from pathlib import Path

here = Path('/home/tritlo/Code/mcfta/lean/restart-evidence/20261022-original-row-physical-meaning')
stem = 'original-row-physical-meaning-strict-1'
assert json.loads((here / (stem + '.json')).read_text())['exit_code'] == 0
assert (here / (stem + '.log')).read_bytes() == b''
assert hashlib.sha256((here / (stem + '.source.lean')).read_bytes()).hexdigest() == 'b3c2aba3c1faf072e318feb7adb07f2b1d60970e4584354ef6584566e053d58e'
expected = {
    'prepare-selected-full.py': '11b20941b21b34065ce6dc6528b4d6a56ca19b449ba14612796e90acdc23da83',
    'check-full-public.py': 'ac93d3ac1442748997d75aced4777366bd891943fdc083aff6703bfbb9515436'}
assert all(not (here / name).exists() for name in expected)
for name, digest in expected.items():
    assert hashlib.sha256((here / 'full-preparation' / name).read_bytes()).hexdigest() == digest
for name in expected:
    shutil.copyfile(here / 'full-preparation' / name, here / name)
print(json.dumps(dict(status='PASS', selected_strict=stem, activated=expected)))
