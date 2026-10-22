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
assert verified['audit_build_jobs'] == 3629 and verified['audit_dependencies'] == 75380
publisher_sha = hashlib.sha256((HERE / 'final-publication.py').read_bytes()).hexdigest()
assert publisher_sha == '2ed5a6d77c61782f76db2c93d167fd6c310a3ad1eb391aecb7928e6245d3fc11'
gate = {
    'status': 'ROOT_ACCEPTED', 'proof_commit': proof,
    'starting_commit': (HERE / 'starting-head.txt').read_text().strip(),
    'publisher_sha256': publisher_sha,
    'actual_audit': 'PASS', 'actual_proof_verification': 'PASS',
    'publication_scope': 'LOCAL_ONLY', 'network_publication': 'PENDING_USER_APPROVAL',
    'seal_at_review': 'PENDING', 'local_publication_at_review': 'PENDING',
    'word_ranges_only': True, 'native_completion_claimed': False,
    'whole_formalization_complete': False,
}
assert not (HERE / 'publication-gate.json').exists()
(HERE / 'publication-gate.json').write_text(json.dumps(gate, indent=2) + '\n')
timestamp = datetime.datetime.now().astimezone().strftime('%Y-%m-%d %H:%M %Z')
progress = HERE / 'current-progress.md'
previous = progress.read_bytes()
prefix = f'''# Current checked checkpoint

Updated: {timestamp}. Proof commit: {proof}.

Official installation, strict1, sole FULL1 and Audit1 pass.
The ledger has three commands: two source and one Audit, all exit zero.
Audit checks 3629 jobs and 75380 theorem dependencies.
Both complete150-line public types remain reviewed and byte-identical.
Saved-evidence verification passes in normal and live modes.
Preservation verifies82469 baseline files and modes,3627 older Lean
sources,298 baseline Haskell files and207 active package files.
No Haskell source or repair changes. FINDINGS keeps its repair index first.
The original44-line source and exact precheck qualification correction remain.
The correction preceded all compiler checks. No failed Lean job is invented.
The theorem derives WordRanges for every actual direct edge-body prefix.
The fixed-source/current-readiness/capacity premises remain explicit.
H6 constructed_node_calls remains the strongest combined semantic theorem.
Native completion and result laws still need separate composition.
The next native-comparison inventory is source-only, not a checked proof.
The local publication gate names the actual proof and reviewed publisher.
Sealing and local publication remain pending at this recorded cut.
Remote publication remains pending fresh user approval after automatic review
rejected the previous push. This local publisher has no network command.
The whole formalization goal stays active and incomplete.

The earlier progress record follows with its original bytes.

'''.encode()
progress.write_bytes(prefix + previous)
assert progress.read_bytes()[len(prefix):] == previous
print(json.dumps({'status': 'PASS', 'proof_commit': proof, 'seal': 'PENDING',
                  'local_publication': 'PENDING', 'network_publication': 'PENDING_USER_APPROVAL'}))
