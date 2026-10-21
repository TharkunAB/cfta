import datetime
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
audit = HERE / 'proof-verifier-repair-audit'
assert hashlib.sha256((audit / 'review.md').read_bytes()).hexdigest() == 'b9ef44f25b4554861349a17f8f5f2c5e1157e330dc5c549e1d0392bcd36ffcf1'
fixed = (HERE / 'verify-proofs.py').read_bytes()
assert fixed == (audit / 'verify-proofs.fixed-147.py.txt').read_bytes()
assert hashlib.sha256(fixed).hexdigest() == '0f200361256dff33d2f40da100fac77169e55be2e827143a9bbbee7ca03349b9'
failure = json.loads(Path('/tmp/mcfta-finite-warm-calls-proof-verification-normal-1.json').read_text())
assert failure['exit_code'] == 1
report = dict(reviewed_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    source_sha256=hashlib.sha256(fixed).hexdigest(), source_lines=len(fixed.splitlines()),
    root_whole_source_and_exact_one_line_repair='CLEAR', independent_review='CLEAR',
    previous_metadata_failure_retained=True, previous_review_retained=True,
    actual_Lean_Lake_jobs=5, new_Lean_Lake_jobs=0,
    normal_live_metadata_execution_authorized=True)
(HERE / 'root-proof-verifier-repair-review.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report))
