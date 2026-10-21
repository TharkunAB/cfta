import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
review = json.loads((HERE / 'root-checkpoint-preparation-review.json').read_text())
assert review['root_whole_final_source_review'] == 'CLEAR'
assert review['independent_final_source_and_pin_review'] == 'CLEAR'
assert review['actual_audit_job'] == 'cold-finite-calls-audit-1'
assert hashlib.sha256((HERE / 'checkpoint-final-pin-audit/review.md').read_bytes()).hexdigest() == review['independent_review_sha256']
pins = {
    'update-documents.py': '6bdf7088427eec8bbda6d0763619b85c2d448c1a65c7101e893be16b7932f6c3',
    'commit-proofs.py': '4904fb074f586578647adba3ad676e739cc8f9e505f4b526c7f280fe646e0520'}
for name, expected in pins.items():
    assert not (HERE / name).exists()
    assert hashlib.sha256((HERE / 'checkpoint-preparation-v2' / name).read_bytes()).hexdigest() == expected
for name in pins:
    (HERE / name).write_bytes((HERE / 'checkpoint-preparation-v2' / name).read_bytes())
print(json.dumps({'status': 'PASS', 'activated_scripts': pins, 'new_proof_jobs': 0}))
