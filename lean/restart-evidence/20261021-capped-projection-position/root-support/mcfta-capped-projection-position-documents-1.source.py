import datetime
import json
import re
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
start = (HERE / 'starting-head.txt').read_text().strip()
proof = (HERE / 'proof-commit-projection.txt').read_text().strip()
selection = json.loads((HERE / 'projection/capped-position-selection.json').read_text())
assert selection['source_sha256'] == '7876487f3271323b0140187bf14ef84cfd23e22d88ff52175c04018ccd8ca436'
audit = (HERE / 'audit-1.log').read_text()
jobs = re.search(r'Build completed successfully \((\d+) jobs\)', audit).group(1)
dependencies = re.search(r'Checked axiom dependencies of (\d+) MicroCFTA theorems', audit).group(1)
assert jobs == '3567'
stamp = datetime.datetime.now().astimezone().strftime('%Y-%m-%d %H:%M %Z')
current = f'''## Current positive paths through actual projection and reads

Updated: {stamp}. Proof checkpoint: `{proof[:10]}`.
Start: `{start[:10]}`. Imported main remains `794903b3f`.
Read `lean/notes-current-capped-projection-position.md`.

For one actual finite-cap projection and the SAME later complete read,
a selected nonplain row comes from the SAME original natural child path.
A selected positive child under a possibly plain row retains the full path
including that ordered child index and its residual path. Both root and child
theorems retain the exact project, read, full row and row index. Root row
indices do not enter child paths. Nullary positive roots are covered.
No input closedness or reader-cost premise is required.

The proof follows the actual read worklist and indexed projection spine.
A union Head can be nonplain; its actual member provenance is retained.
A finite Plain cap forces hereditary Plain only in the Mu case. The proof
excludes positive rows and descendants there using actual full read annotations.
It does not replace a Mu read with empty nodeEdges. Entry semantic readiness,
costs, availability and guard store, reader semantic readiness and guard store,
forward Keeps, and the finite input cap remain explicit.

Root strict has an empty log. Complete two-head readback, independent review
and default Audit pass: {jobs} jobs and {dependencies} dependencies.
Both public heads use only the standard three axioms. Only the old
ClosedCompletion warning remains. Eight actual Lean/Lake jobs include four
retained failed attempts. Copies add no jobs. Counts do not measure completion.
Older proofs, frozen registries, Haskell/package files, stashes, other
worktrees and main remain unchanged. All sealed raw logs must be indexed.

Next, derive the projected endpoint cap from the ORIGINAL false gate and
actual Required Origin. The existing empty-path endpoint_cap supplies its
base case. A nonempty false gate does not cap unrelated sibling branches.
Then compose this inverse with the SAME actual native request and continuation.
The native Return must derive the result cap; no callback ancestry premise
can replace that producer. Source-growth Support is already proved separately.
Selected observations across classes, endpoint barrier preservation,
chronological edits, the retained pair or owner exclusion, general renewal,
final retention, outer completion, convergence and Haskell refinement remain.
The unrestricted opaque-Mu counterexample remains valid.
The full goal stays active. Regular formalize pushes remain authorized.

No Haskell source, runtime result or external repair changes. FINDINGS keeps
the repair registry first and retains every earlier fix and reproducer.
'''
findings = f'''Current proof update: {stamp}. Proof checkpoint: `{proof[:10]}`.
Actual finite-cap projection and the SAME selected complete read now retain
the original positive path. The root theorem covers nonplain nullary rows.
The child theorem covers positive descendants under possibly plain rows,
with the SAME row, ordered child index and full residual path.
Actual read-worklist and indexed-spine provenance are retained.
Union Heads need not be Plain. Mu exclusion uses cap-forced hereditary
Plain and the full actual read annotation. No closedness or reader costs.
Root strict, complete two-head readback, independent review and Audit pass:
{jobs} jobs and {dependencies} dependencies. Only the old ClosedCompletion warning remains.
Eight actual Lean/Lake jobs include four retained failures. Copies add no jobs.

No Haskell source, runtime result or external repair changes.
Preserve PR #97 and every earlier repair and reproducer below.
Original-gate projected caps, the SAME native continuation consumer and
class endpoint barrier preservation,
changed phaseValues and original false-gate transport, renewal, retention,
outer completion, convergence and Haskell correspondence remain open.
Read `lean/notes-current-capped-projection-position.md`. The full goal stays active.
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
note = ROOT / 'lean/notes-current-capped-projection-position.md'
note.write_text(note.read_text() + f'\nSelected proof: `{proof}`. Updated: {stamp}.\nDefault Audit: {jobs} jobs and {dependencies} theorem dependencies.\nActual Lean/Lake jobs: 8. Nonzero jobs: 4.\n')
verifier = HERE / 'verify-checkpoint.py'
text = verifier.read_text()
for old, new in [('AUDIT_DEPENDENCIES_PENDING', dependencies), ('LEAN_JOBS_PENDING', '8'),
                 ('LEAN_FAILURES_PENDING', '4'), ('PUBLIC_THEOREMS_PENDING', '2')]:
    text = text.replace(old, new)
verifier.write_text(text)
print('Updated nine restart documents and the focused projection/read note.')

