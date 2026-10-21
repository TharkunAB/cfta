import datetime
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
start = (HERE / 'starting-head.txt').read_text().strip()
proof = (HERE / 'proof-commit-value.txt').read_text().strip()
now = datetime.datetime.now().astimezone().strftime('%Y-%m-%d %H:%M %Z')
update = f'''## Current positive support and projected-value bridges

Updated: {now}. Proof checkpoint: `{proof[:10]}`.
Start: `{start[:10]}`. Imported main remains `794903b3f`.
Read `lean/notes-current-positive-slot-bridges.md`.

Two small additive modules supply the missing local bridges for actual
target operands. NativePositiveSupportAdvance.advance retains positional
Support through literal unchanged native tables and an actual machine
extension. It transports the SAME captured Origins and Support at the
OLD source, then rebases them at the actual later heap. It supplies no
causal History or new-cell law from growth alone.

RawCorridorPositiveValue.project traces a positive returned value to its
SAME captured input at projectionPath ++ positiveSuffix. An empty PROJECT
path is literal identity, including unions. A nonempty actual projection
returns an ordinary value. Its actual zero-fuel read and exact row/child
use the checked raw observers. No full cap on unrelated input branches,
closure premise or new recursive-exposure framework is added.

Both root strict logs are empty. Complete FULL1/FULL1, independent review
and default Audit pass: 3580 jobs and 74824 dependencies.
Both public theorems use only the standard three axioms.
Eight actual Lean/Lake commands include one retained elaboration failure.
It was fixed by two explicit private header types. Public shapes remain.
Copies add no jobs. Only the old ClosedCompletion Audit warning remains.
Counts do not measure completion. All older sources, registries, evidence,
Haskell/package files, stashes, other worktrees and main remain.
All sealed raw logs must be indexed.

The archived slot-plan now specifies the exact fixed-capture target law.
A completed Force must install positive ancestry at each actual miss and
retain the SAME earlier slot law at a hit. Its operand/Fold/Target joint
induction must produce intermediate caps, both positive stores and actual
causal History. That slot theorem is still an unproved implementation.
Class Rel/common-anchor ancestry, unfinished cuts, historical writer-entry
support, owner exclusion, renewal, retention, outer completion, convergence
and Haskell correspondence remain open. Opaque-Mu counterexamples remain.

Keep the Haskell repair index FIRST in FINDINGS. Insert proof updates AFTER it.
No new Haskell source, runtime result or external repair. All earlier repair
entries remain. The full goal is active. Regular formalize pushes are authorized.
'''
findings = f'''Current proof update: {now}. Proof checkpoint: `{proof[:10]}`.
Two additive bridges now retain positive Support through SAME unchanged
native tables and trace a positive projected value to its SAME raw-corridor
input at projectionPath ++ positiveSuffix. Old-source Origins and actual
Extension justify the Support rebase. They supply no causal History.
Empty PROJECT paths are identity, including unions. Nonempty actual
projections return ordinary values with exact zero-fuel read rows/children.
Root strict, FULL1/FULL1, independent review and Audit pass:
3580 jobs and 74824 dependencies. Both public heads use standard3.
Eight actual Lean/Lake commands include one retained elaboration failure,
fixed by two explicit private header types. Copies add no jobs.
No Haskell source, runtime result or external repair changes.
Actual target-slot ancestry is specified in archived slot-plan and remains
unproved. Class Rel/common anchors, unfinished cuts, historical writer
support, owner exclusion, renewal, retention, outer completion, convergence
and Haskell correspondence remain open. Goal active.
Read `lean/notes-current-positive-slot-bridges.md`. Repair index stays FIRST.
'''
note = f'''# Positive bridges for class target slots

Updated: {now}. Selected proof: `{proof}`.
This checkpoint adds 115 source lines and two public theorems.

`SourceCurrentNativePositiveSupportAdvance.advance` handles actual physical
operations that leave the complete native node and edge tables unchanged.
It takes Current and positive Support at the exact entry heap, Good at the
actual returned checked state, machine Extension and both literal table
equalities. These equalities transport Support and captured Origins to
the SAME returned tables at the OLD source. The existing rebase consumes
those laws, actual growth, issued retention and final Facts. Its result
is positive Support relative to the returned heap. It requires no new
guard, semantic or causal-history premise for this particular law.
It does not derive Support for changed or newly published native cells.
It does not derive causal publication History from physical growth.

`SourceCurrentRawCorridorPositiveValue.project` consumes the SAME actual
projection, input semantic/cost/availability/guard facts, its raw corridor
and PositiveAt of its actual result. Its conclusion is PositiveAt of the
same captured input at projectionPath ++ positiveSuffix. These two paths
are independent. An empty suffix does not make a projection identity.

An empty PROJECT path inverts to literal identity, including a union
input. For a nonempty path, two small private actual-graph shape lemmas
derive Ordinary result from its exact projection and physical effects.
The recursive case uses the actual Head effects. It does not replace
a Mu body by its nodeEdges. A proven ordinary result admits the literal
Read.done 0 at the actual return heap. PositiveAt then selects an exact
root row or ordered child. The existing public raw observers retain that
same read, row and child. Actual effects supply return semantic/guards and
reflexive Keeps. No full-input cap or exposure framework is copied.

Root read all 115 lines and the exact final source delta. The Value proof's
first elaboration failed because two private headers lacked explicit native
types. Its final source adds those two type annotations only. The public
statement and proof route remain. The selected strict and root strict logs
are literally empty. SupportAdvance passes its first strict attempt.
Independent reviews cover both heads and their exact source contracts.

The complete FULL logs have 273850 and 117903 bytes. Both public heads
report only propext, Classical.choice and Quot.sound. All eight printer
settings and complete proofs are checked. No omissions, private public
types or printer fallback are accepted. Five owner commands, two root
strict commands and one default Audit are eight actual Lean/Lake commands.
One elaboration failure remains in the evidence. Copies add no jobs.
Audit passes with 3580 jobs and 74824 theorem dependencies. Only the old
ClosedCompletion unused-variable warning remains. Counts measure checks,
not system completion.

The archived `slot-plan/plan.md` states the next exact target obligation.
For a present slot at action a and every positive suffix q, its full stored
value must trace to the SAME captured forest slot at a competing class path,
followed by q. A miss must derive this law through its actual projections,
Merge winners and native joins before storage. A hit uses that SAME old
slot law. The initial empty target table supplies the old-slot law by absence.
Native positive Support, Merge positive Support and causal History remain
genuine entry laws. They must be produced by the actual preceding calls.
The target proof needs a joint operand/Fold/Target induction because the
old public final-cap endpoint does not expose internal join operand caps.
The new target theorem is still an unproved implementation.

Completed slot ancestry will concern the literal fixed capture of one
class. It will not yet transport changed phase values to the original
forest. Class Rel/common-anchor induction, genuine unfinished Class/Edit/
Force cuts and historical Parent writer-entry stores remain separate.
Owner exclusion, renewal, rank progress, final retention, outer completion,
convergence and Haskell refinement remain open. Opaque-Mu counterexamples
remain valid. No new Haskell defect, repair or runtime result is claimed.
FINDINGS retains the external repair index first and all earlier evidence.
'''
documents = ['NEXT-PROMPT.md', 'HANDOFF.md', 'FINDINGS.md', 'lean/README.md',
             'lean/SYSTEM.md', 'lean/API-COVERAGE.md', 'lean/COVERAGE.md',
             'lean/notes-proof-status-20261017.md', 'lean/notes-current-system-claim.md']
for name in documents:
    original = subprocess.check_output(['git', 'show', start + ':' + name], cwd=ROOT, text=True)
    assert (ROOT / name).read_text() == original, name
    if name == 'FINDINGS.md':
        prefix = '# Current formalization findings\n\n## Haskell fix handoff for external work\n'
        marker = prefix + '\n' + (HERE / 'haskell-repair-index.md').read_text().rstrip() + '\n'
        assert original.startswith(marker)
        rest = original[len(marker):]
        assert rest.startswith('\n')
        changed = marker + '\n' + findings + '\n' + rest[1:]
        assert changed.replace(findings + '\n', '', 1) == original
    else:
        first, rest = original.split('\n', 1)
        changed = first + '\n\n' + update + rest
        assert changed.replace(update + '\n', '', 1) == original
    (ROOT / name).write_text(changed)
(HERE / 'current-update.md').write_text(update)
(HERE / 'findings-update.md').write_text(findings)
(ROOT / 'lean/notes-current-positive-slot-bridges.md').write_text(note)
print('Updated nine documents and focused note. All prior text remains.')
