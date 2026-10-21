import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
review = json.loads((HERE / 'root-proof-verifier-review.json').read_text())
assert review['root_whole_final_source_and_delta_review'] == 'CLEAR'
assert review['independent_whole_final_source_and_delta_review'] == 'CLEAR'
assert hashlib.sha256((HERE / 'proof-verifier-audit/review.md').read_bytes()).hexdigest() == review['independent_review_sha256']
source = (HERE / 'proof-verifier-preparation-v2/verify-proofs.py').read_bytes()
assert hashlib.sha256(source).hexdigest() == '9498f09bcde801fd937723964919a2ab873c52559f82657c7d9486d5d32c61be'
assert len(source.splitlines()) == 180
assert not (HERE / 'verify-proofs.py').exists()
(HERE / 'verify-proofs.py').write_bytes(source)
print(json.dumps({'status': 'PASS', 'source_lines': 180, 'new_proof_jobs': 0}))
