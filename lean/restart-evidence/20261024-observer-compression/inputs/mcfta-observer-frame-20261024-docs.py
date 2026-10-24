import hashlib
import json
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-observer-frame-20261024')
prefix = '''
## Enumeration observations under path compression

Updated: 2026-10-24. Proof: `45585fde7b5e420db64de2c6beed54fb5a128766`.
Start: `ae897030977`. Main refresh found no newer commit than `a5fbb66eec`.
Main is already incorporated. Read `lean/notes-current-observer-compression.md`.

Representative, value and exact public unexpanded-node observations now agree
on framed inputs at independent successful bounds. One successful observation
constructs a finite matching observation in the other input. The full final
frame retains all nonforest fields and every root ID and stored size.
Partial rendering preserves this frame on success. More fuel retains its exact
partial term and final state. Paired partial-render agreement and finite
transport remain the next target. Arbitrary callbacks still need congruence.
The full canonical mutation history and cached-driver bridge remain open.

Strict checks and the installed combined build passed. Audit passed: 3667 jobs,
75754 theorem checks, one replayed older warning and no new-source warning.
All 12 public signatures and 11 axiom reports were read. Evidence retains the
layout failure and the corrected local-instance import collision.
No Haskell source changes. FINDINGS keeps the external repair index FIRST.
Both optional LPO defects remain open. H6 remains strongest combined.
Full-pipeline, resources, width, solver, phase-4 and convergence gaps remain.
H23 remains queued. The full goal is ACTIVE and incomplete.
This record precedes the evidence commit and its authorized push.

'''
names = ['NEXT-PROMPT.md', 'HANDOFF.md', 'FINDINGS.md', 'lean/README.md',
         'lean/SYSTEM.md', 'lean/API-COVERAGE.md', 'lean/COVERAGE.md',
         'lean/notes-proof-status-20261017.md', 'lean/notes-current-system-claim.md']
changes = {}
for name in names:
    path = root / name
    before = path.read_text()
    assert '## Enumeration observations under path compression' not in before
    position = before.index('\n## Canonical cached selection') if name == 'FINDINGS.md' else before.index('\n') + 1
    after = before[:position] + prefix + before[position:]
    path.write_text(after)
    changes[name] = dict(insertion_character=position, inserted=prefix,
                         before_sha256=hashlib.sha256(before.encode()).hexdigest(),
                         after_sha256=hashlib.sha256(after.encode()).hexdigest())
(area / 'document-changes.json').write_text(json.dumps(changes, indent=2) + '\n')
print(json.dumps({'documents': names, 'prefix_lines': len(prefix.splitlines())}))
