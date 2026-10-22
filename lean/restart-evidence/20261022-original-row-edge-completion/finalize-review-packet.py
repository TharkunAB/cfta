import datetime
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
proof = (HERE / 'proof-commit.txt').read_text().strip()
assert proof == '26a01918be8b5a4b2232dbabe3d1ccb8b51a14da'
verified = json.loads((HERE / 'verification.json').read_text())
assert verified['status'] == 'PASS' and verified['actual_jobs'] == 3
publisher = HERE / 'final-publication.py'
publisher_sha = hashlib.sha256(publisher.read_bytes()).hexdigest()
assert publisher_sha == 'aedf9cf3971b9f0f9478f1b38c2b1b02fd20ec76c534d0bab52dff2d540216b9'
gate = {
    'status': 'ROOT_ACCEPTED', 'proof_commit': proof,
    'starting_commit': (HERE / 'starting-head.txt').read_text().strip(),
    'publisher_sha256': publisher_sha,
    'actual_audit': 'PASS', 'actual_proof_verification': 'PASS',
    'seal_at_review': 'PENDING', 'publication_at_review': 'PENDING',
    'semantic_completion_only': True, 'whole_formalization_complete': False,
}
gate_path = HERE / 'publication-gate.json'
assert not gate_path.exists()
gate_path.write_text(json.dumps(gate, indent=2) + '\n')
bounds = ROOT / 'lean/MicroCFTA/SourceCurrentAllocatedNativeRequestBounds.lean'
reservations = ROOT / 'lean/MicroCFTA/SourceCurrentAllocatedFiniteOrdinaryQueryReservations.lean'
assert len(reservations.read_text().splitlines()) == 142
assert 'def WordRanges' in bounds.read_text().splitlines()[133]
erratum = '''# Frozen next-resource inventory citation corrections

The next-resource-inventory component remains byte-identical.
Its A120-128 excerpt does not contain WordRanges.
The actual WordRanges definition is at RequestBounds lines 134-136.
Its S102-146 selection exceeds the 142-line source file.
That saved excerpt contains only lines 102-142 because slicing truncated it.
These are citation defects in a future-work inventory.
They do not change the checked H11 theorem, public type or Audit evidence.
The later direct-edge plan uses strictly bounded source excerpts.
No extra Lean or Lake command was run for these corrections.
'''
assert not (HERE / 'next-resource-inventory-erratum.md').exists()
(HERE / 'next-resource-inventory-erratum.md').write_text(erratum)
timestamp = datetime.datetime.now().astimezone().strftime('%Y-%m-%d %H:%M %Z')
progress = HERE / 'current-progress.md'
previous = progress.read_bytes()
prefix = f'''# Current checked checkpoint

Updated: {timestamp}. Proof commit: {proof}.

Official installation, strict1, sole FULL1 and Audit1 pass.
The ledger has three commands: two source and one Audit, all exit zero.
Audit checks 3628 jobs and 75379 theorem dependencies.
Both complete public types remain reviewed and byte-identical.
Saved-evidence verification passes in normal and live modes.
Preservation verifies 81460 baseline files and modes, 3626 older Lean
sources, 298 baseline Haskell files and 207 active package files.
No Haskell source or repair changes. FINDINGS keeps its repair index first.
The theorem derives semantic completion for actual closed original rows.
H6 constructed_node_calls remains the strongest combined semantic theorem.
Native admission and the full public pass still need separate composition.
The frozen future inventory has two citation corrections in its erratum.
The direct-edge word-ranges plan is source-only and is not a checked proof.
The publication gate names the actual proof commit and reviewed publisher.
Sealing and publication remain pending at this recorded cut.
The whole formalization goal stays active and incomplete.

The earlier progress record follows with its original bytes.

'''.encode()
progress.write_bytes(prefix + previous)
assert progress.read_bytes()[len(prefix):] == previous
print(json.dumps({'status': 'PASS', 'proof_commit': proof, 'seal': 'PENDING', 'publication': 'PENDING'}))
