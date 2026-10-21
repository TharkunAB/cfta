import datetime
import re
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
start = (HERE / 'starting-head.txt').read_text().strip()
proof = (HERE / 'proof-commit-forest-cap.txt').read_text().strip()
audit = (HERE / 'audit-1.log').read_text()
jobs = re.search(r'Build completed successfully \((\d+) jobs\)', audit).group(1)
dependencies = re.search(r'Checked axiom dependencies of (\d+) MicroCFTA theorems', audit).group(1)
assert jobs == '3569'
stamp = datetime.datetime.now().astimezone().strftime('%Y-%m-%d %H:%M %Z')
current = f'''## Current projected caps from the actual Required forest

Updated: {stamp}. Proof checkpoint: `{proof[:10]}`.
Start: `{start[:10]}`. Imported main remains `794903b3f`.
Read `lean/notes-current-required-forest-projection-cap.md`.

Literal requireAll, ORIGINAL false class gates and the SAME actual selected
forest projection now derive a finite cap for that projected endpoint.
The proof derives ChildrenSafe and ordered Origin from the actual Required
receipt ONCE. It retains the SAME original forest index and natural path.
Actual Required effects and forward Keeps derive prepared availability at
the later projection heap. A missing forest slot returns Empty.
No supplied cap, caller Origin, closedness, Merge/native/slot law, current
normality or changed-value false gate is required. Original normality remains
genuine for the Required domain producer. The prepared capture stays fixed.

Root strict has an empty log. Full one-head readback, independent review
and default Audit pass: {jobs} jobs and {dependencies} dependencies.
The theorem uses only the standard three axioms. Only the old ClosedCompletion
warning remains. Four actual Lean/Lake jobs pass. One separate user-bus
launcher failure never started Lean; its exact evidence is retained.
Copies add no jobs. Counts do not measure completion. All older sources,
evidence, frozen registries, Haskell/package files, stashes, other worktrees
and main remain. All sealed raw logs must be indexed.

Next, derive actual Operand caps from this SAME projection and Merge's
conditional returned law, then retain finite target-slot certificates at
their actual Force misses and hits. The compiler places actual edit leaves
at their recorded class paths. Deriving whole native-input caps there still
requires preserved endpoint/corridor conditions across overlapping edits.
Changed phaseValues cannot inherit original false gates without proof.
Chronological class transport, retained pair/owner exclusion, renewal,
final retention, outer completion, convergence and Haskell correspondence
remain open. Unrestricted opaque-Mu counterexamples remain.

Keep the Haskell repair index FIRST in FINDINGS; insert proof updates AFTER it.
No new Haskell source, runtime result or external repair. All earlier repair
entries remain. The full goal is active. Regular formalize pushes are authorized.
'''
findings = f'''Current proof update: {stamp}. Proof checkpoint: `{proof[:10]}`.
The actual literal Required receipt and ORIGINAL false class gates now derive
a finite cap for the SAME selected prepared-forest projection. SAME original
slot/path and ordered Origin are derived, not supplied by a callback.
Keeps and actual Required effects derive later prepared availability.
The missing-slot branch is Empty. No inputcap, caller Origin, closure,
current normality, Merge/native law or changed-value gate is assumed.
Root strict, FULL1, independent review and Audit pass:
{jobs} jobs and {dependencies} dependencies. Only the old ClosedCompletion warning remains.
Four actual Lean/Lake jobs pass. One preserved user-bus launcher failure
did not start Lean and is counted separately. Copies add no jobs.
No Haskell source, runtime result or external repair changes.
Later class-capture endpoint preservation, historical target slots, renewal,
retention, outer completion, convergence and Haskell correspondence remain.
Read `lean/notes-current-required-forest-projection-cap.md`. Goal active.
'''
(HERE / 'current-update.md').write_text(current)
(HERE / 'findings-update.md').write_text(findings)
documents = ['NEXT-PROMPT.md', 'HANDOFF.md', 'FINDINGS.md', 'lean/README.md',
             'lean/SYSTEM.md', 'lean/API-COVERAGE.md', 'lean/COVERAGE.md',
             'lean/notes-proof-status-20261017.md', 'lean/notes-current-system-claim.md']
index = (HERE / 'haskell-repair-index.md').read_text().rstrip()
for name in documents:
    original = subprocess.check_output(['git', 'show', start + ':' + name], cwd=ROOT, text=True)
    assert (ROOT / name).read_text() == original, name
    marker = ('# Current formalization findings\n\n## Haskell fix handoff for external work\n\n' + index + '\n'
              if name == 'FINDINGS.md' else original.split('\n', 1)[0] + '\n')
    block = findings if name == 'FINDINGS.md' else current
    assert original.startswith(marker)
    rest = original[len(marker):]
    assert rest.startswith('\n')
    updated = marker + '\n' + block + '\n' + rest[1:]
    assert updated.replace(block + '\n', '', 1) == original, name
    (ROOT / name).write_text(updated)
note = ROOT / 'lean/notes-current-required-forest-projection-cap.md'
note.write_text(note.read_text() + f'\nSelected proof: `{proof}`. Updated: {stamp}.\nDefault Audit: {jobs} jobs and {dependencies} theorem dependencies.\nActual Lean/Lake jobs: 4. Nonzero Lean jobs: 0. Infrastructure attempts: 1.\n')
verifier = HERE / 'verify-checkpoint.py'
verifier.write_text(verifier.read_text().replace('AUDIT_DEPENDENCIES_PENDING', dependencies))
print('Updated nine restart documents after the first Haskell repair index, plus the focused note.')

