import hashlib
import json
import shutil
from pathlib import Path

here = Path('/home/tritlo/Code/mcfta/lean/restart-evidence/20261022-original-row-cluster-completion')
stem = 'original-row-cluster-completion-strict-3'
assert json.loads((here / (stem + '.json')).read_text())['exit_code'] == 0
assert (here / (stem + '.log')).read_bytes() == b''
assert hashlib.sha256((here / (stem + '.source.lean')).read_bytes()).hexdigest() == 'c6e8e0f7f819d1c595ff6d56c160558bff837a86196ad2c951524d93a70c9a9b'
source = here / 'full-context-repair-v2/prepare-selected-full.py'
assert hashlib.sha256(source.read_bytes()).hexdigest() == 'b4e61b85081c6004f0471b4a1f35d9b9352b8873d15b98da2c42718d3051c26e'
target = here / 'prepare-selected-full.py'
assert not target.exists()
shutil.copyfile(source, target)
print(json.dumps(dict(status='PASS', activated_materializer_sha256=hashlib.sha256(target.read_bytes()).hexdigest(), selected_strict=stem)))
