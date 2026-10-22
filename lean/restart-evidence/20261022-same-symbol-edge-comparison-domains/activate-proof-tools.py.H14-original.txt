import hashlib
import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
review = (HERE / 'actual-binding-audit/review.md').read_bytes()
assert hashlib.sha256(review).hexdigest() == sys.argv[1]
installed = {}
for directory in ['actual-tools-preparation', 'actual-verifier-preparation']:
    source = HERE / directory
    pins = json.loads((source / 'pins.json').read_text())
    for name, expected in pins.items():
        data = (source / name).read_bytes()
        assert hashlib.sha256(data).hexdigest() == expected
        assert b'__H14_' not in data
        target = HERE / name
        assert not target.exists()
        target.write_bytes(data)
        installed[name] = expected
assert len(installed) == 9
print(json.dumps({'status': 'PASS', 'installed_tools': installed, 'new_proof_jobs': 0}))
