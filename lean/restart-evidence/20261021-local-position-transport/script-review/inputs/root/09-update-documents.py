import datetime
import re
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
start = (HERE / 'starting-head.txt').read_text().strip()
proofs = {tag: (HERE / ('proof-commit-' + tag + '.txt')).read_text().strip() for tag in ['maybe-mu', 'target']}
fix = (HERE / 'audit-import-fix-commit.txt').read_text().strip()
audit = (HERE / 'audit-1.log').read_text()
jobs = re.search(r'Build completed successfully \((\d+) jobs\)', audit).group(1)
dependencies = re.search(r'Checked axiom dependencies of (\d+) MicroCFTA theorems', audit).group(1)
assert jobs == '3563'
stamp = datetime.datetime.now().astimezone().strftime('%Y-%m-%d %H:%M %Z')
current = f'''## Current local positive-position transport

Updated: {stamp}. Proofs: `{proofs['maybe-mu'][:10]}` and `{proofs['target'][:10]}`.
Start: `{start[:10]}`. Imported main remains `794903b3f`.
Read `lean/notes-current-local-position-transport.md`.

Actual stored substitution and actual maybeMu now retain each positive
result occurrence at the SAME natural child path in the input or body.
Finite Cap Plain, physical facts and conditional Mu stores remain explicit.
The maybeMu endpoint uses the actual earlier publication history. It covers
open nested binders and earlier warm winners. It uses ONE actual readback
with the CURRENT ordinary callback. It never equates a warm winner's body
with the incoming body. No PlainDomain or desired positional law is assumed.

Actual prepared projection and the literal allocated Target operand now
retain the SAME original forest slot and full path `path ++ residual`.
The operand consumes the literal requireAll return, a selected nonempty
forest path and ORIGINAL false primary gates. It starts at the EXACT prepared
heap. Semantic readiness, normality, costs, GuardHeap Plain, physical Stored
and Merge Support remain explicit. Positive children beneath plain parents
are included. No false gate on the prepared forest is assumed.

Root strict logs are empty. Complete four-head proof readback, separate
independent reviews and default Audit pass: {jobs} jobs and {dependencies}
theorem dependencies. Only the old ClosedCompletion warning remains.
Fourteen actual Lean/Lake jobs include seven retained elaboration failures.
Copies add no jobs. Counts do not measure completion.
An additive import-order fix `{fix[:10]}` places maybeMu before the Audit
command. The publication script and checkpoint verifier now enforce that order.

The main local gap is actual native request/cache positive-source transport.
It needs causal publication history through child returns and a positional
cache law from actual earlier writes. The generic checked-joint Context
does not supply that history. Later Target operands also need transport
from the exact prepared heap through actual intervening calls. Chronological
class edits must then imply the proved normalized path relation and retain
a child pair or exclude owner copying. Original gates cannot be replayed as
prepared gates. General renewal, final retention, outer completion,
convergence and production Haskell refinement remain open.

No Haskell source, runtime result or external fix changes. FINDINGS retains
the repair registry first and all earlier repairs and reproducers.
The full goal stays active. Regular formalize pushes remain authorized.
Publish every sealed path, including ignored raw logs.
'''
findings = f'''Current proof update: {stamp}. Proofs: `{proofs['maybe-mu'][:10]}` and `{proofs['target'][:10]}`.
Actual stored substitution and maybeMu now map positive result paths back
to the SAME input/body paths under finite Cap Plain and genuine heap/store
premises. The maybeMu proof uses actual causal history and the CURRENT
ordinary callback, including open nested binders and earlier warm winners.
Actual prepared projection and the allocated Target operand now recover
the SAME original forest slot and full positive path. The literal requireAll
return and ORIGINAL false gates remain explicit. Operand entry is the EXACT
prepared heap. No prepared false gate or desired positional law is assumed.
Root strict, complete four-head readback, independent reviews and Audit pass:
{jobs} jobs and {dependencies} dependencies, only the old ClosedCompletion warning.
The additive import-order fix `{fix[:10]}` places the new imports before Audit.

No Haskell source, runtime result or external fix changes.
Preserve PR #97 and every earlier repair and reproducer below.
Actual native request/cache transport, causal history through child returns,
later operand heap transport and chronological class edits remain open.
General renewal, retention, outer completion, convergence and Haskell
refinement remain open. The full goal stays active.
Read `lean/notes-current-local-position-transport.md`.
'''
(HERE / 'current-update.md').write_text(current)
(HERE / 'findings-update.md').write_text(findings)
documents = ['NEXT-PROMPT.md', 'HANDOFF.md', 'FINDINGS.md', 'lean/README.md',
             'lean/SYSTEM.md', 'lean/API-COVERAGE.md', 'lean/COVERAGE.md',
             'lean/notes-proof-status-20261017.md', 'lean/notes-current-system-claim.md']
for name in documents:
    original = subprocess.check_output(['git', 'show', start + ':' + name], cwd=ROOT, text=True)
    assert (ROOT / name).read_text() == original, name
    if name == 'FINDINGS.md':
        marker = '# Current formalization findings\n\n## Haskell fix handoff for external work\n'
        block = findings
    else:
        marker = original.split('\n', 1)[0] + '\n'
        block = current
    assert original.startswith(marker)
    rest = original[len(marker):]
    assert rest.startswith('\n'), name
    updated = marker + '\n' + block + '\n' + rest[1:]
    assert updated.replace(block + '\n', '', 1) == original, name
    (ROOT / name).write_text(updated)
note = ROOT / 'lean/notes-current-local-position-transport.md'
text = note.read_text().replace('Updated: 2026-10-21 03:14 CEST.', 'Updated: ' + stamp + '.')
text += f'\nSelected proof commits: `{proofs["maybe-mu"]}` and `{proofs["target"]}`.\nAudit import correction: `{fix}`.\nDefault Audit: {jobs} jobs and {dependencies} theorem dependencies.\nActual Lean/Lake jobs: 14. Retained nonzero elaboration jobs: 7.\n'
note.write_text(text)
verifier = HERE / 'verify-checkpoint.py'
verifier.write_text(verifier.read_text().replace('AUDIT_DEPENDENCIES_PENDING', dependencies))
print('Updated nine restart documents and the new focused note.')
