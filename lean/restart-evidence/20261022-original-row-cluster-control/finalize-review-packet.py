import datetime
import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
proof = (HERE / 'proof-commit.txt').read_text().strip()
assert re.fullmatch('[0-9a-f]{40}', proof)
verified = json.loads((HERE / 'verification.json').read_text())
assert verified['status'] == 'PASS' and verified['actual_jobs'] == 4
assert verified['source_jobs'] == 3 and verified['audit_jobs'] == 1
assert verified['failed_jobs'] == 1
assert verified['warned_source_exit_zero_jobs'] == verified['rejected_public_type_jobs'] == 0
preserved = json.loads((HERE / 'preservation-final.json').read_text())
assert preserved['status'] == 'PASS' and preserved['baseline_files'] == 86577
assert preserved['unchanged_older_non_audit_sources'] == 3631
assert preserved['unchanged_haskell_files'] == 298 and preserved['unchanged_package_files'] == 207
publisher_sha = hashlib.sha256((HERE / 'final-publication.py').read_bytes()).hexdigest()
pins = json.loads((HERE / 'actual-tools-preparation/pins.json').read_text())
assert publisher_sha == pins['final-publication.py']
gate = dict(status='ROOT_ACCEPTED', proof_commit=proof,
    starting_commit=(HERE / 'starting-head.txt').read_text().strip(), publisher_sha256=publisher_sha,
    actual_audit='PASS', actual_proof_verification='PASS', publication_scope='LOCAL_ONLY',
    network_publication='PENDING_USER_APPROVAL', seal_at_review='PENDING',
    local_publication_at_review='PENDING', comparison_lift_derived=True,
    conditional_completed_comparison_premise=True, noncomputable_operational_model=True,
    genuine_packet_cluster_completion_claimed=False, physical_language_iff_claimed=False,
    scan_completion_claimed=False, whole_formalization_complete=False)
assert not (HERE / 'publication-gate.json').exists()
(HERE / 'publication-gate.json').write_text(json.dumps(gate, indent=2) + '\n')
timestamp = datetime.datetime.now().astimezone().strftime('%Y-%m-%d %H:%M %Z')
progress = HERE / 'current-progress.md'
previous = progress.read_bytes()
prefix = f'''# Current checked checkpoint

Updated: {timestamp}. Proof commit: {proof}.

The repaired129-line source passes strict2, sole FULL1 and Audit1.
Strict1 failed with two notation-qualifier errors. Both exact sources and the repair remain.
Strict2 has an empty log. All declaration limits remain unchanged.
The actual ledger has four commands, one failure and no warned source exit-zero command.
Audit checks {verified['audit_build_jobs']} jobs and {verified['audit_dependencies']} theorem dependencies.
Root and independent review read the complete136-line checked public TYPE.
The printed TYPE is byte-identical. No second manual TYPE read is claimed.
Actual axioms are the standard three. Complete output and exact inputs remain.
Normal/live saved checks and preservation pass86577 baseline files/modes,
3631 older Lean sources,298 Haskell files and207 active package files.
The new control reuses the entire H7 State and directly advances its step.
comparison_lift takes an actual completed-past comparison as its observation.
It derives a positive consumed prefix and the exact ordered scan resume at the SAME after.
No genuine-packet cluster completion, semantic law or resource law is added.
H15 remains the comparison and domain-capacity foundation.
H6 constructed_node_calls remains the strongest combined semantic theorem.
Genuine-input cluster completion is next. Physical pruning, grouping, generated parents,
Mu, the public pass, practical host bounds, convergence and Haskell refinement remain open.
The Haskell repair index stays first. No Haskell change or new repair is added.
The full formalization goal stays active and incomplete.
The materializer's amended-header path and nonoverwrite guard are retained exact changes.
Historical rejected verifier and amended exact-header checks remain preserved.
The local gate names the actual proof and reviewed network-free publisher.
Seal and local publication remain pending at this recorded cut.
Remote publication remains pending fresh approval after automatic review rejected the push.

The earlier progress record follows with its original bytes.

'''.encode()
progress.write_bytes(prefix + previous)
assert progress.read_bytes()[len(prefix):] == previous
print(json.dumps({'status': 'PASS', 'proof_commit': proof, 'publisher_sha256': publisher_sha,
    'seal': 'PENDING', 'local_publication': 'PENDING', 'network_publication': 'PENDING_USER_APPROVAL'}))
