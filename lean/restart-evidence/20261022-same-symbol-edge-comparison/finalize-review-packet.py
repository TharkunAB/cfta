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
assert verified['source_jobs'] == 2 and verified['audit_jobs'] == 1
assert verified['failed_jobs'] == verified['warned_source_exit_zero_jobs'] == verified['rejected_public_type_jobs'] == 0
preserved = json.loads((HERE / 'preservation-final.json').read_text())
assert preserved['status'] == 'PASS' and preserved['baseline_files'] == 84279
assert preserved['unchanged_older_non_audit_sources'] == 3629
assert preserved['unchanged_haskell_files'] == 298 and preserved['unchanged_package_files'] == 207
publisher_sha = hashlib.sha256((HERE / 'final-publication.py').read_bytes()).hexdigest()
pins = json.loads((HERE / 'actual-tools-preparation/pins.json').read_text())
assert publisher_sha == pins['final-publication.py']
gate = {
    'status': 'ROOT_ACCEPTED', 'proof_commit': proof,
    'starting_commit': (HERE / 'starting-head.txt').read_text().strip(),
    'publisher_sha256': publisher_sha,
    'actual_audit': 'PASS', 'actual_proof_verification': 'PASS',
    'publication_scope': 'LOCAL_ONLY', 'network_publication': 'PENDING_USER_APPROVAL',
    'seal_at_review': 'PENDING', 'local_publication_at_review': 'PENDING',
    'all_comparison_lookup_cases_and_next_current_invariants_derived': True,
    'native_receipt_on_hits_claimed': False,
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

The original 112-line candidate passes strict1, sole FULL1 and Audit1 unchanged.
All three actual Lean/Lake commands exit zero. Strict has an empty log.
Audit checks {verified['audit_build_jobs']} jobs and {verified['audit_dependencies']} theorem dependencies.
Root and independent review read the complete 728-line checked public TYPE.
The printed TYPE is byte-identical. No second manual TYPE read is claimed.
Actual axioms are the standard three. All complete output slices and exact inputs remain.
Normal/live saved checks and preservation pass 84279 baseline files/modes,
3629 older Lean sources, 298 Haskell files and 207 active package files.
All comparison lookup branches derive completion and final current invariants.
The SAME source/model and genuine current cache and Room premises remain explicit.
No native Receipt on hits, future success, post-Room or physical language iff is claimed.
H6 constructed_node_calls remains the strongest combined semantic theorem.
The next finite-scan capacity investigation is source-only. It has no checked body.
It examines one initial domain cache and actual allocation history across comparisons.
The Haskell repair index stays first. No Haskell change or new repair is added.
The full formalization goal stays active and incomplete.
Three metadata command failures and their exact repairs remain recorded separately.
The gate names the actual local proof and reviewed network-free publisher.
Seal and local publication remain pending at this recorded cut.
Remote publication remains pending fresh approval after automatic review rejected the push.

The earlier progress record follows with its original bytes.

'''.encode()
progress.write_bytes(prefix + previous)
assert progress.read_bytes()[len(prefix):] == previous
print(json.dumps({'status': 'PASS', 'proof_commit': proof, 'publisher_sha256': publisher_sha,
    'seal': 'PENDING', 'local_publication': 'PENDING', 'network_publication': 'PENDING_USER_APPROVAL'}))
