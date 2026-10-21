import datetime
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
assert hashlib.sha256((HERE / 'publisher-pin-audit/review.md').read_bytes()).hexdigest() == 'c4c7a6592d911e89e0d6bdf19b6739a32706c9a376bd9c21186760623bece807'
publisher = (HERE / 'final-publication.py').read_bytes()
assert hashlib.sha256(publisher).hexdigest() == '98e9db21e2d5fba0251f37a10423b06df52514e1aa11ec5a4c735901aa433685'
pending = (HERE / 'checkpoint-tools-preparation/final-publication.py').read_bytes()
proof = (HERE / 'proof-commit.txt').read_text().strip()
assert proof == 'a33536a752d6b299d8767f90d3cc776fe8374b7a'
assert publisher == pending.replace(b'__H5_PROOF_COMMIT__', proof.encode())
verified = json.loads((HERE / 'verification.json').read_text())
assert verified['status'] == 'PASS' and verified['both_proof_verification_modes']
assert json.loads((HERE / 'preservation-final.json').read_text())['status'] == 'PASS'
report = dict(reviewed_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    root_whole_scripts_deltas_and_prose='CLEAR',
    independent_whole_scripts_deltas_and_prose='CLEAR', proof_commit=proof,
    publisher_sha256=hashlib.sha256(publisher).hexdigest(),
    root_owned_verification_terminal='PTY 60649: observed terminal exit 0',
    root_read_current_progress_and_all_new_prelude_text=True,
    publisher_requires_completed_seal=True,
    push_authorized_by_active_user_goal=True, whole_goal_complete=False)
(HERE / 'root-final-checkpoint-review.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report))
