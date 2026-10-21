import datetime
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
start = (HERE / 'starting-head.txt').read_text().strip()
proof = (HERE / 'proof-commit-head.txt').read_text().strip()
now = datetime.datetime.now().astimezone().strftime('%Y-%m-%d %H:%M %Z')
update = f'''## Current positive paths through actual capped Head

Updated: {now}. Proof checkpoint: `{proof[:10]}`.
Start: `{start[:10]}`. Imported main remains `794903b3f`.
Read `lean/notes-current-capped-head-positive.md`.

The SAME actual Head return now has a public positive-path inverse under
its genuine input finite cap and guard heap. The proof retains the actual
underlying Read and its full rows. Actual makeNode readback maps each
positive returned row to a SAME surviving raw read row. Root guards and
ordered child/residual paths remain exact. Public capped observers use
Project.root and that SAME underlying Read at the ORIGINAL reader heap.
No nodeEdges Mu substitution or recursive-exposure framework is added.

Root strict has an empty log. Complete FULL1, independent review and default
Audit pass: 3582 jobs and 74833 dependencies. The sole public theorem uses
only the standard three axioms. All four actual Lean/Lake commands pass.
Copies add no jobs. Only the old ClosedCompletion Audit warning remains.
Counts do not measure completion. All older sources, registries, evidence,
Haskell/package files, stashes, other worktrees and main remain.
All sealed raw logs must be indexed.

The archived rel-plan specifies the next ONE completed-class endpoint.
Its private joint induction must return same-q local input ancestry OR
a source in the SAME class capture with Rel at the exact absolute path.
The new slot theorem supplies the target branch; this Head inverse supplies
the recursive input branch. Exact compiled leaf token/address equality,
actual stores, causal History and constructor NoNewMu remain necessary.
That class theorem is still an unproved implementation. Later positive
chronology, unfinished cuts, historical writer-entry stores, common anchors,
owner exclusion, renewal, retention, outer completion, convergence and
Haskell correspondence remain open. Opaque-Mu counterexamples remain.

Keep the Haskell repair index FIRST in FINDINGS. Insert proof updates AFTER it.
No new Haskell source, runtime result or external repair. All earlier repair
entries remain. The full goal is active. Regular formalize pushes are authorized.
'''
findings = f'''Current proof update: {now}. Proof checkpoint: `{proof[:10]}`.
The SAME actual capped Head now retains every positive path backwards.
Actual underlying Read and makeNode readback recover the SAME complete raw
row and ordered child/residual. Public capped observers run on Project.root
with that SAME Read at the ORIGINAL reader heap. Input cap, semantic/cost,
availability and guard facts remain genuine. No unrestricted opaque-Mu law.
Root strict, complete FULL1, independent review and Audit pass:
3582 jobs and 74833 dependencies. The public head uses standard3.
All four actual Lean/Lake commands pass. Copies add no jobs.
No Haskell source, runtime result or external repair changes.
The archived rel-plan's completed-class joint ancestry theorem is being
implemented and remains unproved. Changed captures, unfinished cuts,
historical writer stores, common anchors, owner exclusion, renewal,
retention, outer completion, convergence and Haskell correspondence remain.
Goal active. Read `lean/notes-current-capped-head-positive.md`.
The external Haskell repair index remains FIRST.
'''
note = f'''# Positive paths through an actual capped Head

Updated: {now}. Selected proof: `{proof}`.
SourceCurrentCappedHeadPositivePosition has 60 lines and one public head.

The theorem takes an actual successful Head graph, entry semantic and cost
facts, input availability, a genuine guard heap, a finite Plain cap on the
COMPLETE input and a PositiveAt witness in the actual returned value.
It concludes PositiveAt in the SAME input at the SAME natural path.
No closedness, causal History or caller row-origin premise is required.
The cap belongs to the input. It is not inferred from a returned cap.

The proof unpacks the SAME Head.read into its actual underlying Read,
raw row list, intermediate heap and makeNode equation. Actual read effects
supply resident rows and semantic facts at that makeNode entry. Actual
constructor readback derives Ordinary result and the surviving normalized
full rows. Every selected positive returned row is a member of the SAME
raw Read rows. Its full guard and ordered children remain literal.
A raw read index is recovered; it need not equal the canonical output
position. Neither an index equality nor occurrence uniqueness is assumed.

For root positivity, the public capped root observer uses Project.root
at the ORIGINAL input heap and that SAME underlying Read. Its reader is
also the original heap, so the original semantic/guard facts and reflexive
Keeps have exact endpoints. The child case retains the same row, ordered
child index, child value and positive residual through the public child
observer. A plain parent row with a positive descendant is included.
A union-positive result is excluded only after Ordinary result is proved.
No Mu read is replaced by nodeEdges Mu. No collector, read induction or
private recursive-exposure framework is copied.

Root read all 60 source lines and the exact public contracts. Independent
review found no mathematical or receipt issue. The first strict source
is final byte-for-byte. Both selected and independent root strict logs
are literally empty. Complete FULL1 contains 100046 bytes with all eight
printer settings, no omissions/private public types or fallback, and only
propext, Classical.choice and Quot.sound. Two owner commands, one root
strict command and one default Audit are four actual Lean/Lake commands.
All pass. Copies add no jobs. Audit passes with 3582 jobs and 74833 theorem
dependencies. Only the old ClosedCompletion warning remains.

The archived rel-plan has zero Lean jobs. It retains one source-range
preparation diagnostic as metadata, without claiming a proof attempt.
It states the exact next completed-class endpoint: preserve the SAME class
Receipt and forward corridors, derive positive native/Merge stores and
causal History, and map every positive returned forest path through
Rel [record.paths] to a literal positive path in the SAME captured forest.

The proposed private subtree conclusion is same-q local input positivity
OR a captured-source Rel witness at the absolute edit address. This is an
induction conclusion, not a caller ancestry premise. Exact compiled leaf
action/address equality is required. Leaf targets use the checked SAME-slot
law and same-q native OR. Recursive Head uses its actual HasLeaf/corridor
finite cap and this public inverse. Constructor-only history must use
History.retain with its actual NoNewMu condition. Growth and issued
extension alone do not construct causal publication History.

The class joint induction is still an unproved implementation. Its scope
is completed ClassReads. Genuine unfinished class/edit/force cut producers
remain separate. Positive relation composition across changed captures,
historical Parent writer-entry stores, and a common original anchor for
two child-separation witnesses remain open. Owner exclusion, renewal,
rank progress, final retention, outer completion, convergence and Haskell
refinement remain open. Opaque-Mu counterexamples remain valid.
No new Haskell source, runtime result or repair is claimed. FINDINGS keeps
its external repair index first and preserves all historical evidence.
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
(ROOT / 'lean/notes-current-capped-head-positive.md').write_text(note)
print('Updated nine documents and focused note. All prior text remains.')
