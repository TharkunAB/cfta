import datetime
import re
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
start = (HERE / 'starting-head.txt').read_text().strip()
proof = (HERE / 'proof-commit-native.txt').read_text().strip()
audit = (HERE / 'audit-1.log').read_text()
jobs = re.search(r'Build completed successfully \((\d+) jobs\)', audit).group(1)
dependencies = re.search(r'Checked axiom dependencies of (\d+) MicroCFTA theorems', audit).group(1)
assert jobs == '3565'
stamp = datetime.datetime.now().astimezone().strftime('%Y-%m-%d %H:%M %Z')
current = f'''## Current actual native requests preserve positive paths

Updated: {stamp}. Proof checkpoint: `{proof[:10]}`.
Start: `{start[:10]}`. Imported main remains `794903b3f`.
Read `lean/notes-current-native-request-position.md`.

For an actual completed closed finite-cap native request at a fixed source,
each positive result occurrence comes from one input at the SAME child path.
Different occurrences can come from different inputs. Both returned native
memo tables retain this law for their full captured requests. The proof uses
the actual trace, actual guard loads, ordered children, causal Mu history,
and the SAME body and result at each memo finish. Ready hits use full
captured-request equality from the physical cache and key-safety facts.

Public Support states the past returned-cell invariant. Public call preserves
Support and derives the result law for an actual supported warm request.
Public request derives both entry cache laws from empty native tables.
Entry Good, source facts, source-resident closed operands, finite Plain caps,
source/current inventory, context and actual causal history remain explicit
where required. The old physical and cap Return is retained. No future
result law or callback is assumed. The theorem consumes a completed trace;
it does not prove that all requests finish.

Root strict has an empty log. Complete three-head readback, independent
review and default Audit pass: {jobs} jobs and {dependencies} dependencies.
All three public heads use only the standard three axioms. Only the old
ClosedCompletion warning remains. Eleven actual Lean/Lake jobs include five
retained failed attempts. Copies add no jobs. Counts do not measure completion.
Older proofs, frozen registries, Haskell/package files, stashes, other
worktrees and main remain unchanged. All sealed raw logs must be indexed.

Next, rebase Support to a later source using actual SAME-cell origins.
A 49-line candidate is separate and is not part of this checkpoint.
Then prove selected-observation transport across actual Head/native class
continuations. Finite OR-input positive support alone is insufficient through
opaque Mu. Across classes the captured phaseValues change; original false
gates cannot be applied to changed captures without proof. The unrestricted
opaque-Mu counterexample remains valid outside this finite-cap theorem.
Chronological class edits, the retained pair or owner exclusion, general
renewal, final retention, outer completion, convergence and Haskell refinement
remain open. The full goal stays active. Regular formalize pushes remain authorized.

No Haskell source, runtime result or external repair changes. FINDINGS keeps
the repair registry first and retains every earlier fix and reproducer.
'''
findings = f'''Current proof update: {stamp}. Proof checkpoint: `{proof[:10]}`.
An actual completed closed finite-cap native request now derives the SAME
positive-path origin law for its result and for both returned memo tables.
The warm call requires the genuine current past-cell Support invariant.
The cold request derives the entry laws from empty tables. Actual causal
Mu history, full captured requests, SAME body/result finishes, physical
admission, source facts, closed available inputs and Plain caps are retained.
This is a conditional result for actual completed traces, not termination.
Root strict, full three-head readback, independent review and Audit pass:
{jobs} jobs and {dependencies} dependencies. Only the old ClosedCompletion warning remains.
Eleven actual Lean/Lake jobs include five retained failures. Copies add no jobs.

No Haskell source, runtime result or external repair changes.
Preserve PR #97 and every earlier repair and reproducer below.
Same-cell source rebasing, selected observations across changed class
captures, general renewal, retention, outer completion, convergence and
Haskell refinement remain open. The unrestricted opaque-Mu counterexample
is retained. Read `lean/notes-current-native-request-position.md`.
The full goal stays active.
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
note = ROOT / 'lean/notes-current-native-request-position.md'
note.write_text(note.read_text() + f'\nSelected proof: `{proof}`. Updated: {stamp}.\nDefault Audit: {jobs} jobs and {dependencies} theorem dependencies.\nActual Lean/Lake jobs: 11. Nonzero jobs: 5.\n')
verifier = HERE / 'verify-checkpoint.py'
verifier.write_text(verifier.read_text().replace('AUDIT_DEPENDENCIES_PENDING', dependencies))
print('Updated nine restart documents and the focused native request note.')

