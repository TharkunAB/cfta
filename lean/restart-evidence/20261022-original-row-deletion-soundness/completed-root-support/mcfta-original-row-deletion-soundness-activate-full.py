import hashlib
import json
import shutil
from pathlib import Path

here = Path('/home/tritlo/Code/mcfta/lean/restart-evidence/20261022-original-row-deletion-soundness')
stem = 'original-row-deletion-soundness-strict-1'
assert json.loads((here / (stem + '.json')).read_text())['exit_code'] == 0
assert (here / (stem + '.log')).read_bytes() == b''
assert hashlib.sha256((here / (stem + '.source.lean')).read_bytes()).hexdigest() == 'a4dd0cdd8a73cdd0e0a87f4ef668f9708cbee9b9132108424411772a8c91ae0a'
assert len((here / (stem + '.source.lean')).read_bytes().splitlines()) == 105
assert hashlib.sha256((here / 'full-reader-audit/review.md').read_bytes()).hexdigest() == 'd390f94b998109b3c47fd569eb63fa900b5b835c0f078f3dc21d74c6a16ebc62'
expected = {
    'prepare-selected-full.py': '1eca3b6914901f8aebb38be5e26975fbed7f3b1c48996d9a3405ab9fb85ba96a',
    'check-full-public.py': '5b6de82fb62cad65f417ba1fd586b34382100439fef2ef572cd53ce3b105f7a4'}
assert all(not (here / name).exists() for name in expected)
for name, digest in expected.items():
    assert hashlib.sha256((here / 'full-preparation' / name).read_bytes()).hexdigest() == digest
for name in expected:
    shutil.copyfile(here / 'full-preparation' / name, here / name)
print(json.dumps(dict(status='PASS', selected_strict=stem, activated=expected)))
