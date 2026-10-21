import datetime
import re
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
start = (HERE / 'starting-head.txt').read_text().strip()
proof = (HERE / 'proof-commit-chronology.txt').read_text().strip()
audit = (HERE / 'audit-1.log').read_text()
jobs = re.search(r'Build completed successfully \((\d+) jobs\)', audit).group(1)
dependencies = re.search(r'Checked axiom dependencies of (\d+) MicroCFTA theorems', audit).group(1)
assert jobs == '3575'
stamp = datetime.datetime.now().astimezone().strftime('%Y-%m-%d %H:%M %Z')
current = f'''## Current chronological raw endpoint preservation

Updated: {stamp}. Proof checkpoint: `{proof[:10]}`.
Start: `{start[:10]}`. Imported main remains `794903b3f`.
Read `lean/notes-current-class-corridor-chronology.md`.

The SAME actual successful class right fold now preserves every incoming
raw corridor in its corresponding returned value, plus current native and
stored Merge laws. A head uses its literal tail-produced phaseValues.
The tail's SAME Receipt supplies readiness, admission, availability, domains,
physical stores, coverage and global validity. Its ordered All₂ relation
transfers the head's ORIGINAL entry mask at the SAME selected forest index.
The actual class theorem produces the next laws. Relations compose in order.

Public fold and pass retain the complete SAME Receipt. Final Empty
propagation keeps the checked state and Merge table. Public indexed_phase
retains the exact source occurrence, actual tail/call/later graphs and all
three reads with their drop/take schedules. Its SAME tail receipt, phase
Current/Merge laws and All₂ relation concern those exact phaseValues.
No native History premise or output is added. Initial all-record masks,
domains and genuine warm current/Merge laws remain explicit.

Root strict has an empty log. Complete FULL3, independent review and default
Audit pass: {jobs} jobs and {dependencies} dependencies.
All three public theorems use only the standard three axioms.
Five actual Lean/Lake jobs include one retained failed elaboration.
Selected strict and FULL logs are clean. Only the old ClosedCompletion
Audit warning remains. Copies add no jobs. Counts do not measure completion.
All older sources, registries, evidence, Haskell/package files, stashes,
other worktrees and main remain. All sealed raw logs must be indexed.

Next, integrate the actual selected Required entry producers and carry
positive native Support with SAME-cell Origins and causal publication
History through actual query returns. Completed fold/phase preservation
does not certify an unfinished class or a pending native cut.
Chronological positive ancestry, retained pair/owner exclusion, renewal,
final retention, outer completion, convergence and Haskell correspondence
remain open. Unrestricted opaque-Mu counterexamples remain.

Keep the Haskell repair index FIRST in FINDINGS. Insert proof updates AFTER it.
No new Haskell source, runtime result or external repair. All earlier repair
entries remain. The full goal is active. Regular formalize pushes are authorized.
'''
findings = f'''Current proof update: {stamp}. Proof checkpoint: `{proof[:10]}`.
The SAME actual successful class right fold, final propagated pass and
indexed phase cut now retain every original raw corridor in ordered values.
Each head uses its actual tail-produced phaseValues. The SAME tail Receipt
supplies physical facts and domains. Its All₂ relation transfers original
head masks at the SAME forest index. Current native and Merge laws remain.
Indexed phases retain the exact tail/call/later graphs, reads and schedules.
No changed false gate or native History premise is added. Initial raw masks,
domains and genuine prior warm stores remain explicit.
Root strict, complete FULL3, independent review and Audit pass:
{jobs} jobs and {dependencies} dependencies. Only the old ClosedCompletion warning remains.
Five actual Lean/Lake jobs include one retained elaboration failure.
All three public heads use standard3. Copies add no jobs.
No Haskell source, runtime result or external repair changes.
Actual Required integration, SAME-query positive Support/Origins/history,
unfinished-cut invariants, positive ancestry, renewal, retention, outer
completion, convergence and Haskell correspondence remain open.
Read `lean/notes-current-class-corridor-chronology.md`. Goal active.
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
note = ROOT / 'lean/notes-current-class-corridor-chronology.md'
note.write_text(note.read_text() + f'\nSelected proof: `{proof}`. Updated: {stamp}.\nDefault Audit: {jobs} jobs and {dependencies} theorem dependencies.\nActual Lean/Lake jobs: 5. Nonzero Lean jobs: 1.\n')
verifier = HERE / 'verify-checkpoint.py'
verifier.write_text(verifier.read_text().replace('AUDIT_DEPENDENCIES_PENDING', dependencies))
print('Updated nine restart documents after the first Haskell repair index, plus the focused note.')

