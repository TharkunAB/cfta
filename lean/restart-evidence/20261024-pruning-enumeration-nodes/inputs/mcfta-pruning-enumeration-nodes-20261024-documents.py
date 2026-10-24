import hashlib
import json
import subprocess
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-pruning-enumeration-nodes-20261024')
baseline = '4c856a02c12a6fa2ff67e7780d5afa709a1a86a5'
proof = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root).decode().strip()
assert subprocess.check_output(['git', 'rev-list', '--parents', '-n', '1', proof], cwd=root).decode().split() == [proof, baseline]
note = area / 'current-note.md'
text = note.read_text()
assert '\nProof:' not in text
text = text.replace('Main: `74250bd889685da436cdbfe32ac4b5a0878ffd09`, incorporated.',
    'Main: `74250bd889685da436cdbfe32ac4b5a0878ffd09`, incorporated.\nProof: `' + proof + '`.')
note.write_text(text)
destination = root / 'lean/notes-current-pruning-enumeration-nodes.md'
assert not destination.exists()
destination.write_bytes(note.read_bytes())
prefix = '''
## Stored enumeration-node handles

Updated: 2026-10-24. Main `74250bd88` is incorporated.
Proof: `PROOF_HASH`.
Read `lean/notes-current-pruning-enumeration-nodes.md`.

A computed heap decoder now derives exact complete-value readback for closed
available inputs under Coherent. It checks the issued key and canonical winner
before the payload. Missing entries and losing reservations return none. Actual
Keeps growth preserves every successful lookup. Empty0/positiveID+1 is a model
handle convention; raw native NodeId extraction and raw UVar IDs stay separate.

Strict checking and the installed build pass. Audit passes 3680 jobs and 76095
dependency checks, with one older warning and no new-source warning. All four
signatures and two actual axiom reports were read. Both reports contain only
propext and Quot.sound. The failed first proof and frozen proposal remain.

Next derive initial pending-slot realization and connect actual observations
to complete available closed Values. Preserve realization through frames, cache
growth and actual slot writes. Then compose outer narrow, typing and memo2 with
typedTypes. Native extraction, graph realization, global helper canonicality,
mutation histories, selected-current protection, cached scheduling, semantic
pruning, phase 4, resources, practical width, runtime/solver and convergence stay
open. H6 remains strongest combined. H23 stays queued. No Haskell source changes.
FINDINGS keeps its external repair index FIRST. All six recorded fixes are on
main. The full goal is ACTIVE and incomplete. This precedes evidence and push.

'''.replace('PROOF_HASH', proof)
paths = ['NEXT-PROMPT.md', 'HANDOFF.md', 'FINDINGS.md', 'lean/README.md',
    'lean/SYSTEM.md', 'lean/API-COVERAGE.md', 'lean/COVERAGE.md',
    'lean/notes-proof-status-20261017.md', 'lean/notes-current-system-claim.md']
changes = {}
for name in paths:
    path = root / name
    before = path.read_text()
    assert path.read_bytes() == subprocess.check_output(['git', 'show', baseline + ':' + name], cwd=root)
    position = before.index('## Actual interned-node narrowing and emptiness') if name == 'FINDINGS.md' else before.index('\n') + 1
    after = before[:position] + prefix + before[position:]
    path.write_text(after)
    changes[name] = dict(insertion_character=position, inserted=prefix,
        before_sha256=hashlib.sha256(before.encode()).hexdigest(),
        after_sha256=hashlib.sha256(after.encode()).hexdigest())
(area / 'document-changes.json').write_text(json.dumps(changes, indent=2) + '\n')
(area / 'proof-commit.json').write_text(json.dumps(dict(commit=proof, baseline=baseline,
    paths=['lean/MicroCFTA/SourcePruningEnumerationNodes.lean', 'lean/MicroCFTA/Audit.lean']), indent=2) + '\n')
print(json.dumps(dict(documents=paths, note=str(destination), proof=proof)))
