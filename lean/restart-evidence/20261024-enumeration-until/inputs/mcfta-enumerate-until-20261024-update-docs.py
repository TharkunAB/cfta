import hashlib, json
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-enumerate-until-20261024')
prefix = '''## Shared enumeration: checked eager completion bridge

Updated: 2026-10-24. Proof: `ecabbf38e669d96275ce991fa8a843bcec3b51ed`.
Start: `790c39ce21`. Imported main remains `6b62b4afef`.
Read `lean/notes-current-enumeration-until.md`.

The additive model now includes stop, narrowing, shallow preparation, both callbacks,
repeated recursion and partial rendering on the existing enumeration state.
For read-only callbacks, its no-stop, identity-narrowing, eager specialization
has exactly the old ordered successful rows at the SAME finite bound.
Duplicates and complete final states are retained. Old Unit results become none.
The equivalence needs no Safe or completion premise. With Safe before, the
existing completion theorem gives Safe after, counter growth and Finished.
Earlier implementation and proof bodies remain unchanged. Audit adds one import.

This is a bridge between two actions with the same modeled scan scheduler.
Actual Haskell cached scheduling and path-compressing observers need a separate
observational bridge. Error rows and callback traces are not equated.
The public shallow API changes fragment observations; disabling its stop rule
does not make arbitrary pruning callbacks eager-equivalent. Partial holes can
have no accepted completion. No additional Haskell repair is claimed here.
FINDINGS keeps the negative-depth repair and both open LPO defects FIRST.

Strict Lean and the installed module builds passed. Audit passed: 3659 jobs,
75635 dependency checks, one replayed older warning and no new-source warning.
Compiled public statements and axioms were read. Evidence retains failed attempts.
H6 remains strongest combined. Full-pipeline, resource, width, source/solver and
convergence gaps remain. H23 counter composition remains queued. The goal is ACTIVE.
This section supersedes the enumeration target in the older main-refresh report.
The next step is cached-selection and observing-callback correspondence.
This record precedes the evidence commit and its authorized push.

'''
paths = ['NEXT-PROMPT.md', 'HANDOFF.md', 'FINDINGS.md', 'lean/README.md',
         'lean/SYSTEM.md', 'lean/API-COVERAGE.md', 'lean/COVERAGE.md',
         'lean/notes-proof-status-20261017.md', 'lean/notes-current-system-claim.md']
changes = {}
for relative in paths:
    path = root / relative
    old = path.read_text()
    if relative == 'FINDINGS.md':
        anchor = '## Imported main: partial program enumeration and term orders\n'
        index = old.index(anchor)
    else:
        index = old.index('\n') + 1
        if old[index:index+1] == '\n':
            index += 1
    assert prefix not in old
    new = old[:index] + '\n' + prefix + old[index:]
    path.write_text(new)
    changes[relative] = dict(before_sha256=hashlib.sha256(old.encode()).hexdigest(),
                             after_sha256=hashlib.sha256(new.encode()).hexdigest(),
                             insertion_character=index, inserted='\n'+prefix)
(area / 'document-changes.json').write_text(json.dumps(changes, indent=2)+'\n')
