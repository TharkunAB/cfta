import hashlib
import json
import subprocess
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
here = root / 'lean/restart-evidence/20261022-prepend-grouping'
assert hashlib.sha256((here / 'full-tool-audit/review.md').read_bytes()).hexdigest() == 'cc1c4c3c082d54adcc1128f5b7a5616c037cc4c06cccbb4183264556448fcf75'
source_sha = '3d293c27b502aa308c8cc05f21796264b18f873221b3343910e77d6bcb6b53ba'
gate = json.loads((here / 'root-source-review-v4.json').read_text())
assert gate['status'] == 'ROOT_WHOLE_SOURCE_REVIEW_CLEAR' and gate['source_sha256'] == source_sha
strict = 'prepend-grouping-strict-3'
receipt = json.loads((here / (strict + '.json')).read_text())
assert receipt['exit_code'] == 0 and receipt['sha256'] == source_sha
assert (here / (strict + '.log')).read_bytes() == b''
assert not list(here.glob('prepend-grouping-public-*.json'))
preparation = here / 'full-preparation'
pins = json.loads((preparation / 'pins.json').read_text())
assert isinstance(pins, list) and len(pins) == 22
for pin in pins:
    raw = (preparation / pin['path']).read_bytes()
    assert len(raw) == pin['bytes'] and hashlib.sha256(raw).hexdigest() == pin['sha256']
for name in ['prepare-selected-full.py', 'check-full-public.py']:
    target = here / name
    assert not target.exists()
    target.write_bytes((preparation / name).read_bytes())
subprocess.run(['/usr/bin/python3', str(here / 'prepare-selected-full.py'), strict, source_sha, '89',
    '50a6a280046eea149e67e07683153558840c8bd7e5465104d32bd8f1e230cdda', '6',
    'c903f09c4f52b0db58dd5c94dbb85e765d5d84905666bc4f9216f567c16c333f', '49'],
    cwd='/', check=True)
print(json.dumps(dict(status='PASS', strict=strict, source_sha256=source_sha, full_job_authorized=True)))
