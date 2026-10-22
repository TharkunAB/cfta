import hashlib
import json
import shutil
import sys
from pathlib import Path

here = Path('/home/tritlo/Code/mcfta/lean/restart-evidence/20261022-original-row-cluster-language')
stem, expected_sha, expected_lines, source_gate = sys.argv[1:]
def sha(data):
    return hashlib.sha256(data).hexdigest()
gate = json.loads((here / source_gate).read_text())
assert gate['status'] == 'ROOT_ACCEPTED_FOR_ONE_STRICT_CHECK_ONLY'
assert gate['source_sha256'] == expected_sha and gate['source_lines'] == int(expected_lines)
assert json.loads((here / (stem + '.json')).read_text())['exit_code'] == 0
assert (here / (stem + '.log')).read_bytes() == b''
source = (here / (stem + '.source.lean')).read_bytes()
assert sha(source) == expected_sha and len(source.splitlines()) == int(expected_lines) <= 500
assert sha((here / 'full-reader-audit/review.md').read_bytes()) == 'e91fed2c819e98626915b23496b0341a0fc8cdee5eed9f32449f9f2558dfeb50'
expected = {
    'prepare-selected-full.py': 'cc873c0f262351396aa7eed067624bb2dbd20203e36f2d42f0a7c137c708fe26',
    'check-full-public.py': '3ae45e59ff5ab313e2b8824ea67b25ad214d2e5a5f6248dd74db322e45fdfcf3'}
assert all(not (here / name).exists() for name in expected)
for name, digest in expected.items():
    assert sha((here / 'full-preparation' / name).read_bytes()) == digest
for name in expected:
    shutil.copyfile(here / 'full-preparation' / name, here / name)
print(json.dumps(dict(status='PASS', selected_strict=stem, activated=expected)))
