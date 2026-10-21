import datetime
import re
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
start = (HERE / 'starting-head.txt').read_text().strip()
proof = (HERE / 'proof-commit-rebase.txt').read_text().strip()
audit = (HERE / 'audit-1.log').read_text()
jobs = re.search(r'Build completed successfully \((\d+) jobs\)', audit).group(1)
dependencies = re.search(r'Checked axiom dependencies of (\d+) MicroCFTA theorems', audit).group(1)
assert jobs == '3566'
stamp = datetime.datetime.now().astimezone().strftime('%Y-%m-%d %H:%M %Z')
current = f'''## Current positive native support at later source heaps

Updated: {stamp}. Proof checkpoint: `{proof[:10]}`.
Start: `{start[:10]}`. Imported main remains `794903b3f`.
Read `lean/notes-current-native-support-rebase.md`.

Positive native memo Support now rebases to a later source heap.
The native state, full captured requests, results, child indices and paths
stay the SAME. Actual per-cell Origins move legitimate later bindings and
inputs back to the old source. The old Support law then applies directly.
Both table bounds and links stay unchanged. Source facts, Grows, issued
identity extension and the SAME-cell Origins remain explicit.

This removes the source-growth obstruction for this invariant. It does not
derive Origins from Support or growth, or prove that a generated request
finishes. The fixed-source call/request theorem still consumes an actual
completed trace. A consumer must obtain Origins and the old store from the
SAME actual trace or current Frame and keep actual causal history.

Root strict has an empty log. Complete one-head readback, independent review
and default Audit pass: {jobs} jobs and {dependencies} dependencies.
The public theorem uses only the standard three axioms. Only the old
ClosedCompletion warning remains. Four actual Lean/Lake jobs have no
failures. Copies add no jobs. Counts do not measure completion.
Older proofs, frozen registries, Haskell/package files, stashes, other
worktrees and main remain unchanged. All sealed raw logs must be indexed.

The next substantial gap is selected-observation transport across actual
Head/native class continuations. A finite-cap projection/read inversion is
a proposed local subcase. It is not yet proved here. Finite OR-input support
alone cannot recover observations hidden by opaque Mu. Across classes the
phaseValues capture changes; original false gates remain on original values.
Chronological edits, the retained pair or owner exclusion, general renewal,
final retention, outer completion, convergence and Haskell refinement remain.
The unrestricted opaque-Mu counterexample stays valid.
The full goal stays active. Regular formalize pushes remain authorized.

No Haskell source, runtime result or external repair changes. FINDINGS keeps
the repair registry first and retains every earlier fix and reproducer.
'''
findings = f'''Current proof update: {stamp}. Proof checkpoint: `{proof[:10]}`.
Positive native memo Support now remains valid at a later source heap for
the SAME native state and full captured node and edge requests. Actual
SAME-cell Origins pull later bindings and inputs back to the old source.
Source facts, Grows and issued identity extension remain explicit.
No result, handle, path, table bound or link is changed. No execution,
completion, causal-history or origin producer is assumed to follow from growth.
Root strict, complete one-head readback, independent review and Audit pass:
{jobs} jobs and {dependencies} dependencies. Only the old ClosedCompletion warning remains.
Four actual Lean/Lake jobs pass. Copies add no jobs.

No Haskell source, runtime result or external repair changes.
Preserve PR #97 and every earlier repair and reproducer below.
Selected observations across actual class continuations and changed captures,
general renewal, retention, outer completion, convergence and Haskell
correspondence remain open. The unrestricted opaque-Mu counterexample stays.
Read `lean/notes-current-native-support-rebase.md`. The full goal stays active.
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
note = ROOT / 'lean/notes-current-native-support-rebase.md'
note.write_text(note.read_text() + f'\nSelected proof: `{proof}`. Updated: {stamp}.\nDefault Audit: {jobs} jobs and {dependencies} theorem dependencies.\nActual Lean/Lake jobs: 4. Nonzero jobs: 0.\n')
verifier = HERE / 'verify-checkpoint.py'
verifier.write_text(verifier.read_text().replace('AUDIT_DEPENDENCIES_PENDING', dependencies))
print('Updated nine restart documents and the focused source rebase note.')

