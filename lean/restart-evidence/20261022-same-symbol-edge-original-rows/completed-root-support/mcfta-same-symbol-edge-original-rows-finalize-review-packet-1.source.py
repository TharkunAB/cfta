import datetime
import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
proof = (HERE / 'proof-commit.txt').read_text().strip()
assert re.fullmatch('[0-9a-f]{40}', proof)
verified = json.loads((HERE / 'verification.json').read_text())
assert verified['status'] == 'PASS' and verified['actual_jobs'] == 3
assert verified['audit_build_jobs'] == 3630 and verified['audit_dependencies'] == 75383
publisher_sha = hashlib.sha256((HERE / 'final-publication.py').read_bytes()).hexdigest()
assert publisher_sha == '49cd99b95378989e0e4642b320b9310d133fb09d4b25e62f5af70a157ca2a4e9'
gate = {
    'status': 'ROOT_ACCEPTED', 'proof_commit': proof,
    'starting_commit': (HERE / 'starting-head.txt').read_text().strip(),
    'publisher_sha256': publisher_sha,
    'actual_audit': 'PASS', 'actual_proof_verification': 'PASS',
    'publication_scope': 'LOCAL_ONLY', 'network_publication': 'PENDING_USER_APPROVAL',
    'seal_at_review': 'PENDING', 'local_publication_at_review': 'PENDING',
    'native_completion_and_stable_idle_derived': True,
    'post_call_room_claimed': False, 'physical_language_iff_claimed': False,
    'whole_formalization_complete': False,
}
assert not (HERE / 'publication-gate.json').exists()
(HERE / 'publication-gate.json').write_text(json.dumps(gate, indent=2) + '\n')
timestamp = datetime.datetime.now().astimezone().strftime('%Y-%m-%d %H:%M %Z')
progress = HERE / 'current-progress.md'
previous = progress.read_bytes()
prefix = f'''# Current checked checkpoint

Updated: {timestamp}. Proof commit: {proof}.

The174-line original candidate passes strict1, sole FULL1 and Audit1 unchanged.
All three actual Lean/Lake commands exit zero. Strict has an empty log.
Audit checks3630 jobs and75383 theorem dependencies. Its old warning remains.
Root and an independent reviewer read the complete1085-line checked TYPE.
The printed TYPE is independently byte-identical. No second manual read is claimed.
Actual axioms are the standard three. All output slices and exact inputs remain.
Normal/live saved checks and full preservation pass83325 baseline files/modes,
3628 older Lean sources,298 Haskell files and207 active package files.
The SAME native Receipt/result/full after, final Stable/native Idle and returned
pair cells are derived. Current source/model/cache and Room premises remain explicit.
No future success, post-call Room or physical language iff is supplied or claimed.
H6 constructed_node_calls remains the strongest combined semantic theorem.
The future branch-free comparison inventory is source-only and has no body or check.
Its frozen authorship error has a separate erratum. Haskell repair index stays first.
No Haskell change or new repair is added. The full formalization goal stays active.
The gate names the actual local proof and reviewed network-free publisher.
Seal and local publication remain pending at this recorded cut.
Remote publication remains pending fresh approval after automatic review rejected the push.

The earlier progress record follows with its original bytes.

'''.encode()
progress.write_bytes(prefix + previous)
assert progress.read_bytes()[len(prefix):] == previous
print(json.dumps({'status': 'PASS', 'proof_commit': proof,
    'seal': 'PENDING', 'local_publication': 'PENDING', 'network_publication': 'PENDING_USER_APPROVAL'}))
