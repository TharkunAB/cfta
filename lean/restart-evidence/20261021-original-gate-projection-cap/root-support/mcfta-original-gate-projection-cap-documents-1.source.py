import datetime
import re
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
start = (HERE / 'starting-head.txt').read_text().strip()
proof = (HERE / 'proof-commit-gate-cap.txt').read_text().strip()
audit = (HERE / 'audit-1.log').read_text()
jobs = re.search(r'Build completed successfully \((\d+) jobs\)', audit).group(1)
dependencies = re.search(r'Checked axiom dependencies of (\d+) MicroCFTA theorems', audit).group(1)
assert jobs == '3568'
stamp = datetime.datetime.now().astimezone().strftime('%Y-%m-%d %H:%M %Z')
current = f'''## Current local caps from original false gates

Updated: {stamp}. Proof checkpoint: `{proof[:10]}`.
Start: `{start[:10]}`. Imported main remains `794903b3f`.
Read `lean/notes-current-original-gate-projection-cap.md`.

The ORIGINAL false gate and actual Required Origin now derive a finite cap
for the SAME actual projected endpoint. No supplied input cap, closedness,
initial UnionNormal or changed-value false gate is required. Original and
prepared values, exact path, gate scan, projection and heaps stay explicit.
The proof uses endpoint_cap at an empty path, zero_clear/reaches_cap for
the finite shortcut, and actual annotations for accepted Mu corridors.
Ordered Origin maps retain each selected child. Actual open ReadAll/Union
and Head effects retain caps and guards. Unrelated siblings may remain opaque.

Root strict has an empty log. Full one-head readback, independent review
and default Audit pass: {jobs} jobs and {dependencies} dependencies.
The public theorem uses only the standard three axioms. Only the old
ClosedCompletion warning remains. Five actual Lean/Lake jobs include one
retained failed attempt. Copies add no jobs. Counts do not measure completion.
Older proofs, registries, Haskell/package files, stashes, other worktrees
and main are preserved. All sealed raw logs must be indexed.

Next, the literal Required forest wrapper must derive the SAME Origin from
its actual preparation receipt and retain its selected original slot.
Its 88-line candidate is separate and not part of this checkpoint.
Changed phaseValues still need actual endpoint/corridor preservation across
all later class paths. SAME native continuation composition, chronological
class edits, retained pair/owner exclusion, general renewal, final retention,
outer completion, convergence and Haskell correspondence remain open.
The unrestricted opaque-Mu counterexample remains valid.

FINDINGS now starts with a short external repair index. Keep that index
before proof updates. Insert later proof updates AFTER the repair index.
No new Haskell source, runtime result or repair changes. All historical
repairs, reproductions and validation remain. Goal active; pushes authorized.
'''
proof_update = f'''Current proof update: {stamp}. Proof checkpoint: `{proof[:10]}`.
The ORIGINAL false gate and actual Required Origin now derive a finite cap
for the SAME actual projected endpoint. No supplied cap, closedness,
initial UnionNormal or changed-value gate is required. The exact original
path, gate and actual open projection remain. Unrelated siblings may be opaque.
Root strict, full one-head readback, independent review and Audit pass:
{jobs} jobs and {dependencies} dependencies. Only the old ClosedCompletion warning remains.
Five actual Lean/Lake jobs include one retained failure. Copies add no jobs.
No Haskell source, runtime result or external repair changes.
The actual Required forest wrapper and later changed-capture corridor
preservation remain separate. Renewal, retention, outer completion,
convergence and Haskell correspondence remain open.
Read `lean/notes-current-original-gate-projection-cap.md`. Goal active.
'''
findings = (HERE / 'haskell-repair-index.md').read_text().rstrip() + '\n\n' + proof_update
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
note = ROOT / 'lean/notes-current-original-gate-projection-cap.md'
note.write_text(note.read_text() + f'\nSelected proof: `{proof}`. Updated: {stamp}.\nDefault Audit: {jobs} jobs and {dependencies} theorem dependencies.\nActual Lean/Lake jobs: 5. Nonzero jobs: 1.\n')
verifier = HERE / 'verify-checkpoint.py'
text = verifier.read_text()
for old, new in [('AUDIT_DEPENDENCIES_PENDING', dependencies), ('LEAN_JOBS_PENDING', '5'),
                 ('LEAN_FAILURES_PENDING', '1'), ('PUBLIC_THEOREMS_PENDING', '1')]:
    text = text.replace(old, new)
verifier.write_text(text)
print('Updated nine restart documents, the focused note and the first external repair index.')

