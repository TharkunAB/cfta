import datetime
import re
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
start = (HERE / 'starting-head.txt').read_text().strip()
proof = (HERE / 'proof-commit-corridor-cap.txt').read_text().strip()
audit = (HERE / 'audit-1.log').read_text()
jobs = re.search(r'Build completed successfully \((\d+) jobs\)', audit).group(1)
dependencies = re.search(r'Checked axiom dependencies of (\d+) MicroCFTA theorems', audit).group(1)
assert jobs == '3573'
stamp = datetime.datetime.now().astimezone().strftime('%Y-%m-%d %H:%M %Z')
current = f'''## Current raw endpoint conditions and target caps

Updated: {stamp}. Proof checkpoint: `{proof[:10]}`.
Start: `{start[:10]}`. Imported main remains `794903b3f`.
Read `lean/notes-current-raw-corridor-target-caps.md`.

Three additive modules now connect actual Required, raw endpoint conditions,
actual projection and shared target forcing. RawCorridor bounds a whole
region or checks the SAME selected child in EVERY raw ordinary row.
Literal requireAll and ORIGINAL false class gates derive every selected
prepared corridor, with the SAME original forest slot and ordered Origin.
Unrelated siblings need no supplied whole-value cap.

The SAME actual open Project derives a finite Plain cap from its raw
corridor. Its proper forest wrapper checks only the actual selected root.
Actual open reads, chronological guard heaps, max bounds and normalized
unions retain the output cap. No closedness premise is added.
The generic actual Force now consumes raw corridors on its literal capture.
It reuses the existing native/Merge/finite-slot invariant. It preserves the
actual Merge winner, checked fold, miss certificate and SAME earlier hit.
Its captured values can be later phaseValues once their corridors are proved.
Native/Merge entry laws and actual readiness remain explicit.

Root strict logs are empty. FULL4/FULL2/FULL1, independent review and default
Audit pass: {jobs} jobs and {dependencies} dependencies. One inductive and
six theorems are public. Each reports only the standard three axioms.
Fourteen actual Lean/Lake jobs include three temporary canonical builds and
one retained import-layout failure. One earlier successful pass has two
constructor documentation warnings. One approval-tool timeout started no
process and adds no Lean job. Only the old ClosedCompletion Audit warning
remains. Copies and theorem counts do not measure completion.
All older sources, registries, evidence, Haskell/package files, stashes,
other worktrees and main remain. All sealed raw logs must be indexed.

Next, derive raw-condition preservation through the SAME actual class edit.
Its 390-line draft has root review; it is not part of this checkpoint.
Chronological class composition must then retain corridors on each actual
tail-produced phaseValues. Original gates remain on original values.
Positive-path transport, retained pair/owner exclusion, renewal, final
retention, outer completion, convergence and Haskell correspondence remain
open. Unrestricted opaque-Mu counterexamples remain.

Keep the Haskell repair index FIRST in FINDINGS. Insert proof updates AFTER it.
No new Haskell source, runtime result or external repair. All earlier repair
entries remain. The full goal is active. Regular formalize pushes are authorized.
'''
findings = f'''Current proof update: {stamp}. Proof checkpoint: `{proof[:10]}`.
Actual Required and ORIGINAL false class gates now derive every selected
prepared raw corridor, with its SAME original slot and ordered Origin.
Raw corridors retain every raw selected row child or a finite whole region.
The SAME actual open projection derives its finite Plain cap. Its proper
forest wrapper checks only the selected root. No closedness premise.
Actual shared target forcing now uses raw corridors of its own literal
captured values, retaining native/Merge laws and same-value slot caps through
misses and hits. No all-captured-root cap or changed-value gate is required.
Root strict, FULL4/FULL2/FULL1, independent review and Audit pass:
{jobs} jobs and {dependencies} dependencies. Only the old ClosedCompletion warning remains.
Fourteen actual Lean/Lake jobs include three temporary canonical builds and
one retained import-layout failure. An unselected successful pass has two
constructor documentation warnings. One prelaunch tool timeout adds no job.
All seven public heads report only the standard three axioms. Copies add no jobs.
No Haskell source, runtime result or external repair changes.
Actual class-edit raw-condition preservation is a reviewed draft, separate
from this checkpoint. Changed-capture chronology, positive-path transport,
renewal, retention, outer completion, convergence and Haskell correspondence
remain open. Read `lean/notes-current-raw-corridor-target-caps.md`. Goal active.
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
note = ROOT / 'lean/notes-current-raw-corridor-target-caps.md'
note.write_text(note.read_text() + f'\nSelected proof: `{proof}`. Updated: {stamp}.\nDefault Audit: {jobs} jobs and {dependencies} theorem dependencies.\nActual Lean/Lake jobs: 14. Nonzero Lean jobs: 1. Temporary canonical jobs: 3.\n')
verifier = HERE / 'verify-checkpoint.py'
verifier.write_text(verifier.read_text().replace('AUDIT_DEPENDENCIES_PENDING', dependencies))
print('Updated nine restart documents after the first Haskell repair index, plus the focused note.')

