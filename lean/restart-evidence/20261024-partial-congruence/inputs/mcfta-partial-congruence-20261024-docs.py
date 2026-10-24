import hashlib
import json
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-partial-congruence-20261024')
prefix = '''
## Partial rendering: agreement and finite transport

Updated: 2026-10-24. Proof: `29776e8b6fcff0fecc34061775933646da576a70`.
Start: `51505458d39`. Imported main remains `a5fbb66eec`.
Read `lean/notes-current-partial-congruence.md`.

Successful partial renders now agree across the complete compression frame.
One observed success constructs a finite matching render in the related input.
The literal root-read and partial-render sequence has the same results, with
one common bound within each run and independent bounds across the two runs.
The proof retains actual intermediate states, child order, original hole IDs
and the empty-constraint recursive truncation branch. It needs no Finished,
Safe or accepted-completion premise. Totality alone does not prove termination.

Strict checks and the installed combined build passed. Audit passed: 3671 jobs,
75775 theorem checks, one replayed older warning and no new-source warning.
All 11 public signatures and 11 axiom reports were read. Evidence retains all
three failed attempts and their narrow elaboration repairs.
Next, prove the actual Pruning.resume and templateOracle observer behavior.
Complete canonical mutation histories and the cached-driver bridge remain open.
No Haskell source changes. FINDINGS keeps the external repair index FIRST.
Both LPO defects remain open. H6 remains strongest combined. H23 remains queued.
Full-pipeline, resources, width, solver, phase-4 and convergence gaps remain.
The full goal is ACTIVE and incomplete. This record precedes the authorized push.

'''
names = ['NEXT-PROMPT.md', 'HANDOFF.md', 'FINDINGS.md', 'lean/README.md',
         'lean/SYSTEM.md', 'lean/API-COVERAGE.md', 'lean/COVERAGE.md',
         'lean/notes-proof-status-20261017.md', 'lean/notes-current-system-claim.md']
changes = {}
for name in names:
    path = root / name
    before = path.read_text()
    assert '## Partial rendering: agreement and finite transport' not in before
    position = before.index('\n## Enumeration observations') if name == 'FINDINGS.md' else before.index('\n') + 1
    after = before[:position] + prefix + before[position:]
    path.write_text(after)
    changes[name] = dict(insertion_character=position, inserted=prefix,
                         before_sha256=hashlib.sha256(before.encode()).hexdigest(),
                         after_sha256=hashlib.sha256(after.encode()).hexdigest())
(area / 'document-changes.json').write_text(json.dumps(changes, indent=2) + '\n')
print(json.dumps({'documents': names, 'prefix_lines': len(prefix.splitlines())}))
