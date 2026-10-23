import hashlib
import json
import subprocess
from pathlib import Path

HERE = Path('/home/tritlo/Code/mcfta/lean/restart-evidence/20261023-pair-stable-model-transport')
stem = 'pair-stable-model-transport-strict-1'
source_sha = '69a294d6519b9029480175702b8025b1b1a32a1d2328e3c24b6ad0916972610f'
assert json.loads((HERE / (stem + '.json')).read_text())['exit_code'] == 0
assert (HERE / (stem + '.log')).read_bytes() == b''
source = (HERE / (stem + '.source.lean')).read_bytes()
assert hashlib.sha256(source).hexdigest() == source_sha and len(source.splitlines()) == 41
report = dict(status='ROOT_ACCEPTED_CLEAN_STRICT_FOR_FULL', source_sha256=source_sha,
    source_lines=41, selected_strict=stem, strict_log_literal_empty=True,
    actual_jobs=1, failed_jobs=0, full_jobs=0, official_install_authorized=False)
(HERE / 'root-source-review.json').write_text(json.dumps(report, indent=2) + '\n')
subprocess.run(['/usr/bin/python3', str(HERE / 'prepare-selected-full.py'), stem, source_sha, '41',
    'bd4f607090408dbfd71e806d57d1ce53c0c450972d6f99053a560f9767708513', '9',
    'a38f167161a41cffaf98549658dbed045f8f54e87c9d32f4a4de4d8dc03293fc', '16'], check=True)
print(json.dumps(report))
