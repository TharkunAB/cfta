import datetime
import re
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
start = (HERE / 'starting-head.txt').read_text().strip()
proof = (HERE / 'proof-commit-later.txt').read_text().strip()
audit = (HERE / 'audit-1.log').read_text()
jobs = re.search(r'Build completed successfully \((\d+) jobs\)', audit).group(1)
dependencies = re.search(r'Checked axiom dependencies of (\d+) MicroCFTA theorems', audit).group(1)
assert jobs == '3564'
stamp = datetime.datetime.now().astimezone().strftime('%Y-%m-%d %H:%M %Z')
current = f'''## Current target positions at later supported heaps

Updated: {stamp}. Proof checkpoint: `{proof[:10]}`.
Start: `{start[:10]}`. Imported main remains `794903b3f`.
Read `lean/notes-current-target-later-position.md`.

The literal allocated Target operand can now start at a later supported
heap while reading the SAME prepared forest. Keeps retains physical records
and issued identities. Actual Required effects and Keeps derive current
prepared availability. Current SemanticReady, CostHeap and GuardHeap Plain,
physical Stored and Merge Support remain explicit. A positive returned
occurrence at q retains the SAME original forest index and `path ++ q`.
The saved Merge memo retains Support. The theorem consumes the actual
requireAll return and ORIGINAL false class gates. No prepared false gate,
current UnionNormal or exact prepared-heap equality is assumed.

Root strict has an empty log. Complete one-head readback, independent review
and default Audit pass: {jobs} jobs and {dependencies} theorem dependencies.
Only the old ClosedCompletion warning remains. Four actual Lean/Lake jobs
have no failures. Copies add no jobs. Counts do not measure completion.
Older proofs, frozen registries, Haskell/package files, stashes, other
worktrees and main remain unchanged. All sealed raw logs must be indexed.

Within one class the capture stays fixed while heaps advance. Across classes
the captured tail-return forest changes. The theorem does not identify that
changed forest with prepared. Actual native request/cache positional support
still needs causal Mu history through child returns and actual finish-derived
warm laws. A bounded finite-cap source-scoped proof is underway separately.
Complete class transport also needs SAME selected-observation/native/Head
continuations through opaque Mu. Finite OR-input support alone is insufficient.
Original gates cannot be applied to changed phaseValues without proof.
Chronological edits, the retained pair or owner exclusion, general renewal,
final retention, outer completion, convergence and Haskell refinement remain.

No Haskell source, runtime result or external repair changes. FINDINGS keeps
the repair registry first and retains every earlier fix and reproducer.
The full goal stays active. Regular formalize pushes remain authorized.
'''
findings = f'''Current proof update: {stamp}. Proof checkpoint: `{proof[:10]}`.
The actual allocated Target operand now retains the SAME original forest
slot and full positive path when its prepared capture is read at a later
supported heap. Keeps and actual Required effects derive prepared Values.
Current SemanticReady, costs, GuardHeap Plain, Stored and Merge Support
remain explicit. Literal requireAll and ORIGINAL false gates are retained.
No prepared false gate or exact entry-heap equality is assumed.
Root strict, complete one-head readback, independent review and Audit pass:
{jobs} jobs and {dependencies} dependencies, only the old ClosedCompletion warning.
Four actual Lean/Lake jobs pass. Copies add no jobs.

No Haskell source, runtime result or external repair changes.
Preserve PR #97 and every earlier repair and reproducer below.
Native request/cache support, causal history through child returns,
selected observations across changed class captures, renewal, retention,
outer completion, convergence and Haskell refinement remain open.
The full goal stays active. Read `lean/notes-current-target-later-position.md`.
'''
(HERE / 'current-update.md').write_text(current)
(HERE / 'findings-update.md').write_text(findings)
documents = ['NEXT-PROMPT.md', 'HANDOFF.md', 'FINDINGS.md', 'lean/README.md',
             'lean/SYSTEM.md', 'lean/API-COVERAGE.md', 'lean/COVERAGE.md',
             'lean/notes-proof-status-20261017.md', 'lean/notes-current-system-claim.md']
for name in documents:
    original = subprocess.check_output(['git', 'show', start + ':' + name], cwd=ROOT, text=True)
    assert (ROOT / name).read_text() == original, name
    marker = ('# Current formalization findings\n\n## Haskell fix handoff for external work\n'
              if name == 'FINDINGS.md' else original.split('\n', 1)[0] + '\n')
    block = findings if name == 'FINDINGS.md' else current
    assert original.startswith(marker)
    rest = original[len(marker):]
    assert rest.startswith('\n')
    updated = marker + '\n' + block + '\n' + rest[1:]
    assert updated.replace(block + '\n', '', 1) == original, name
    (ROOT / name).write_text(updated)
note = ROOT / 'lean/notes-current-target-later-position.md'
note.write_text(note.read_text() + f'\nSelected proof: `{proof}`. Updated: {stamp}.\nDefault Audit: {jobs} jobs and {dependencies} theorem dependencies.\nActual Lean/Lake jobs: 4. Nonzero jobs: 0.\n')
verifier = HERE / 'verify-checkpoint.py'
verifier.write_text(verifier.read_text().replace('AUDIT_DEPENDENCIES_PENDING', dependencies))
print('Updated nine restart documents and the new focused note.')
