import datetime
import re
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
start = (HERE / 'starting-head.txt').read_text().strip()
proof = (HERE / 'proof-commit-shared-cap.txt').read_text().strip()
audit = (HERE / 'audit-1.log').read_text()
jobs = re.search(r'Build completed successfully \((\d+) jobs\)', audit).group(1)
dependencies = re.search(r'Checked axiom dependencies of (\d+) MicroCFTA theorems', audit).group(1)
assert jobs == '3570'
stamp = datetime.datetime.now().astimezone().strftime('%Y-%m-%d %H:%M %Z')
current = f'''## Current finite caps through actual target misses and hits

Updated: {stamp}. Proof checkpoint: `{proof[:10]}`.
Start: `{start[:10]}`. Imported main remains `794903b3f`.
Read `lean/notes-current-required-shared-target-cap.md`.

The SAME actual target Force now preserves current native and Merge laws
and a finite cap for every exact present slot value. A miss derives each
competing operand cap from its own actual Required-forest projection and
the ORIGINAL false class gates. The actual Merge returned law covers warm
winners. The fold raises the two depths to their maximum at the SAME checked
native query. It stores the cap of that exact returned target. A hit uses
the old certificate of the SAME slot value. Empty slots start vacuously.
Current native and stored Merge laws remain genuine entry premises.
Coherence and Nontrivial derive proper competing paths. The actual prepared
capture stays fixed; unrelated prepared roots need no whole-value cap.

Root strict has an empty log. Full three-head readback, independent review
and default Audit pass: {jobs} jobs and {dependencies} dependencies.
The structure and both theorems each use only the standard three axioms.
Only the old ClosedCompletion warning remains. Five actual Lean/Lake jobs
include one retained failed elaboration. Copies add no jobs. Counts do not
measure completion. All older sources, evidence, frozen registries,
Haskell/package files, stashes, other worktrees and main remain.
All sealed raw logs must be indexed.

Next, preserve raw endpoint conditions for ALL selected paths through
overlapping class edits. The exact compiler leaf path equals its recorded
class path. Completed projected caps alone do not cap raw edit inputs:
projection can remove dead rows. Later classes capture actual tail results,
so fixed prepared captures cannot stand in for changed phaseValues.
Original false gates do not automatically transfer to changed values.
Chronological positive-path transport, retained pair/owner exclusion,
renewal, final retention, outer completion, convergence and Haskell
correspondence remain open. Unrestricted opaque-Mu counterexamples remain.

Keep the Haskell repair index FIRST in FINDINGS; insert proof updates AFTER it.
No new Haskell source, runtime result or external repair. All earlier repair
entries remain. The full goal is active. Regular formalize pushes are authorized.
'''
findings = f'''Current proof update: {stamp}. Proof checkpoint: `{proof[:10]}`.
The SAME actual target Force now preserves finite caps through misses and
same-slot hits. Each miss operand uses its exact Required-forest projection
and ORIGINAL false gates. The actual Merge winner and chronological checked
intersection retain its cap. A miss stores that same result with its cap;
a hit reuses the old certificate for the exact value in the same slot.
Current native and stored Merge laws remain explicit. Coherent plus
Nontrivial supplies proper paths. The actual prepared capture stays fixed.
No all-prepared-root caps or changed-value false gates are required.
Root strict, FULL3, independent review and Audit pass:
{jobs} jobs and {dependencies} dependencies. Only the old ClosedCompletion warning remains.
Five actual Lean/Lake jobs include one preserved failed elaboration.
The structure and both theorems each use the standard three axioms.
Copies add no jobs. No Haskell source, runtime result or repair changes.
Raw all-path conditions through overlapping edits, later changed captures,
chronological positive-path transport, renewal, retention, outer completion,
convergence and Haskell correspondence remain open.
Read `lean/notes-current-required-shared-target-cap.md`. Goal active.
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
note = ROOT / 'lean/notes-current-required-shared-target-cap.md'
note.write_text(note.read_text() + f'\nSelected proof: `{proof}`. Updated: {stamp}.\nDefault Audit: {jobs} jobs and {dependencies} theorem dependencies.\nActual Lean/Lake jobs: 5. Nonzero Lean jobs: 1.\n')
verifier = HERE / 'verify-checkpoint.py'
verifier.write_text(verifier.read_text().replace('AUDIT_DEPENDENCIES_PENDING', dependencies))
print('Updated nine restart documents after the first Haskell repair index, plus the focused note.')

