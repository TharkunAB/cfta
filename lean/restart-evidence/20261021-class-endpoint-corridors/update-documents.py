import datetime
import re
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
start = (HERE / 'starting-head.txt').read_text().strip()
proof = (HERE / 'proof-commit-class-corridor.txt').read_text().strip()
audit = (HERE / 'audit-1.log').read_text()
jobs = re.search(r'Build completed successfully \((\d+) jobs\)', audit).group(1)
dependencies = re.search(r'Checked axiom dependencies of (\d+) MicroCFTA theorems', audit).group(1)
assert jobs == '3574'
stamp = datetime.datetime.now().astimezone().strftime('%Y-%m-%d %H:%M %Z')
current = f'''## Current raw endpoint preservation through actual class edits

Updated: {stamp}. Proof checkpoint: `{proof[:10]}`.
Start: `{start[:10]}`. Imported main remains `794903b3f`.
Read `lean/notes-current-class-endpoint-corridors.md`.

The SAME actual successful class edit now preserves EVERY incoming raw
corridor in the corresponding returned value. Its ordered All₂ relation
covers paths above, below and outside each edited path. Exact compiled leaf
pairs derive placement in the immutable original input. A leaf obtains a
finite whole input cap, then uses its SAME actual target Force and checked
query. Actual row/child reconstruction and canonical survivors retain the
same path positions. A recursive HasLeaf supplies a whole finite input;
actual open Head transport and the body edit derive its whole output cap.

The theorem returns the SAME class Receipt, current native laws and stored
Merge laws. It derives leaf results through actual calls. No output callback,
whole-root cap or changed-value false gate is supplied. Genuine entry
readiness, admission, projection domains, availability, physical Merge
storage, coverage, global memo validity, current native/Merge laws and raw
masks for the captured class remain explicit. Coherence and Nontrivial remain.

Root strict has an empty log. Complete public readback, independent review
and default Audit pass: {jobs} jobs and {dependencies} dependencies.
The sole public theorem uses only the standard three axioms.
Seven actual Lean/Lake jobs include two retained failed elaborations and
one unselected warning-only success. Selected strict and FULL logs are clean.
Only the old ClosedCompletion Audit warning remains. Copies add no jobs.
Counts do not measure completion. All older sources, registries, evidence,
Haskell/package files, stashes, other worktrees and main remain.
All sealed raw logs must be indexed.

Next, compose this ordered preservation through the actual tail-first class
fold. Each head must use its literal tail-produced phaseValues and receipt.
Original false gates remain on the original forest. Chronological positive
ancestry, retained pair/owner exclusion, renewal, final retention, outer
completion, convergence and Haskell correspondence remain open.
Unrestricted opaque-Mu counterexamples remain.

Keep the Haskell repair index FIRST in FINDINGS. Insert proof updates AFTER it.
No new Haskell source, runtime result or external repair. All earlier repair
entries remain. The full goal is active. Regular formalize pushes are authorized.
'''
findings = f'''Current proof update: {stamp}. Proof checkpoint: `{proof[:10]}`.
One SAME actual successful class edit now preserves every incoming raw
corridor in its corresponding returned value, through an ordered All₂ law.
Exact compiler leaf pairs derive immutable input placement. Actual target
Force and checked native queries derive finite leaf outputs. Ordered rows,
canonical survivors and actual recursive Head/body calls retain corridors.
The theorem returns the SAME class Receipt plus native and Merge cap laws.
Entry masks, readiness, domains and warm store laws remain genuine premises.
No supplied output callback, all-root cap or changed-value false gate.
Root strict, full public readback, independent review and Audit pass:
{jobs} jobs and {dependencies} dependencies. Only the old ClosedCompletion warning remains.
Seven actual Lean/Lake jobs include two retained elaboration failures and
one unselected warning-only success. The public theorem uses standard3.
Copies add no jobs. No Haskell source, runtime result or external repair changes.
Tail-first class-fold composition on actual phaseValues, positive ancestry,
renewal, retention, outer completion, convergence and Haskell correspondence
remain open. Read `lean/notes-current-class-endpoint-corridors.md`. Goal active.
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
note = ROOT / 'lean/notes-current-class-endpoint-corridors.md'
note.write_text(note.read_text() + f'\nSelected proof: `{proof}`. Updated: {stamp}.\nDefault Audit: {jobs} jobs and {dependencies} theorem dependencies.\nActual Lean/Lake jobs: 7. Nonzero Lean jobs: 2.\n')
verifier = HERE / 'verify-checkpoint.py'
verifier.write_text(verifier.read_text().replace('AUDIT_DEPENDENCIES_PENDING', dependencies))
print('Updated nine restart documents after the first Haskell repair index, plus the focused note.')

