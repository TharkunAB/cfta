import datetime
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
data = (HERE / 'proof-verifier-preparation/verify-proofs.py').read_bytes()
assert hashlib.sha256(data).hexdigest() == '81ed5c293a008a30cd6b21fceb576ad4c338b2c10da771c9b176ba5d9895c9c0'
assert len(data.splitlines()) == 147
review = HERE / 'proof-verifier-audit/review.md'
assert hashlib.sha256(review.read_bytes()).hexdigest() == 'a3ca2f0fba8658fe947323824c1909910d0263e7695a9ecbc1535e80c6711713'
assert not (HERE / 'verify-proofs.py').exists()
(HERE / 'verify-proofs.py').write_bytes(data)
report = dict(reviewed_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    whole_147_line_source_and_122_line_delta_root_review='CLEAR',
    independent_whole_source_review='CLEAR', source_sha256=hashlib.sha256(data).hexdigest(),
    actual_proof_jobs=5, failed_jobs=1, warned_source_exit_zero_jobs=1,
    new_Lean_Lake_jobs=0, metadata_verification_authorized=True)
(HERE / 'root-proof-verifier-review.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report))
