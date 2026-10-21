import datetime
import hashlib
import json
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
start = (HERE / 'starting-head.txt').read_text().strip()
proof = (HERE / 'proof-commit-rank.txt').read_text().strip()
now = datetime.datetime.now().astimezone().strftime('%Y-%m-%d %H:%M %Z')
assert hashlib.sha256((ROOT / 'lean/MicroCFTA/SourceCurrentActualChildRank.lean').read_bytes()).hexdigest() == 'f4f2e895519d57d582a4422676cc3bca3b1896c95868883698bc2a5e7361f3d4'
assert not (HERE / 'rank-strict-1.log').read_bytes()
audit = (HERE / 'audit-1.log').read_text()
assert 'Build completed successfully (3608 jobs)' in audit and '75033 MicroCFTA theorems' in audit
assert {v['path'] for v in json.loads((HERE / 'components.json').read_text())} == {'rank', 'independent-review', 'body-plan'}
full = (HERE / 'rank/actual-child-rank-public-1.log').read_bytes()
assert len(full) == 17758839 and hashlib.sha256(full).hexdigest() == '0a160c4edf65db46a006736308311716790dcd0c76adadb857ccbd6eecc26bc9'
update = f'''## Current actual child dispatch strictly decreases a request measure

Updated: {now}. Proof checkpoint: `{proof[:10]}`.
Start: `{start[:10]}`. Imported main remains `794903b3f`.
Read `lean/notes-current-actual-child-rank.md`.

ActualChildRank.dispatch now proves strict lexicographic decrease for an
actual recursive child request. The first component counts inherited
positive-path equality classes. The second component is structural mass.
The same literal ordinary container must contain the original source row.
The theorem returns the selected child's actual Reached prefix as well.
It needs no evaluating owner cell, copied-owner equality or collision.

Genuine initial resources, laws and writer Origins remain explicit. The
actual row, Parent, live inherited prefix and earlier child walk identify
the same current states. One resource-backed Written supplies full positive
Back and conditional Shape. The checked quotient count gives a weak bound
for every child and a strict bound for a nonplain source row. A plain row
has empty own equalities. Its returned original child or Empty has strictly
smaller mass. The actual late descent identifies the inherited payload,
including a cached winning result. No future child completion is assumed.

This proves one actual call transition. The archived next plan composes
these transitions through an older owner's body prefix. Each hop must use
its own row membership. Actual activation must identify the complete
captured request from the same current canonical store. That composition
is a separate target. Older-owner exclusion, finite renewal bounds, final
retention, outer completion, convergence, broader initial resources and
Haskell refinement remain open. Whole-library termination is not proved.

Strict, complete FULL, independent review and Audit pass. Audit has
3608 jobs /75033 dependencies. Eight actual Lean/Lake commands retain four
failed strict checks. Strict4 also contains one unused-simp warning.
The four repairs select the Bool lemma, specify existing container fields
and order the exact payload rewrite before wrapper reduction. The sole
71-line public header remains unchanged. Selected/root strict logs are
empty. Whole checked/printed type identity, all eight printer settings and
the actual standard three axioms pass. The 250-line prelaunch draft and
private unused-output trim to 248 lines remain zero-job evidence. Final
source has 249 lines. Full raw errors, patches and lossless root review
metadata remain. No canonical, infrastructure, constructed, runtime or
reviewer proof job ran. Only the old Audit warning remains in the Audit.
Counts are not completion.

All older proof/evidence bytes and version exceptions remain. Haskell,
packages, imported main, stashes and other worktrees stay unchanged.
No new Haskell defect or repair. FINDINGS keeps its external repair index
FIRST. Work continues as requested.
'''
findings = f'''Current proof update: {now}. Proof checkpoint: `{proof[:10]}`.
An actual recursive child request now strictly decreases inherited positive
class count followed by structural mass. The literal original row belongs
to the same ordinary container. Actual current resources supply Back,
Shape and the late descended payload, including cached winners. No active
owner cell, collision, supplied rank or future completion is required.

Strict/FULL/independent review/Audit pass: 3608 jobs /75033 dependencies.
Eight actual commands retain four failed strict checks and their exact
repairs. Strict4 is a warned failure. Public header, all eight settings,
whole type identity and standard axioms pass. Original prelaunch sources,
all raw logs and lossless root diagnostic reviews remain. No canonical,
infrastructure, constructed, runtime or reviewer proof job ran.
Older body-prefix composition is next. Older-owner exclusion, finite
renewals, retention, completion, convergence, broader initial resources and
Haskell refinement remain open. This is not a termination theorem.
No Haskell source, runtime result or external repair changes.
Read `lean/notes-current-actual-child-rank.md`.
The external Haskell repair index stays FIRST. Counts are not completion.
'''
note = '# Strict decrease for actual child dispatch\n\n' + update + '''
The sole public theorem is SourceCurrentActualChildRank.dispatch.
Its final source has 249 lines and SHA256
f4f2e895519d57d582a4422676cc3bca3b1896c95868883698bc2a5e7361f3d4.
Its declaration matches the frozen 71-line proposal byte for byte.

The measure is (PositiveQuotientCount.count inheritedRecords value,
InternedValueMass.value value), ordered by Prod.Lex Nat.lt Nat.lt.
Fuel is not a component. The container needs row membership, not an active
cache entry. Union, Mu and reference children need no additional premise.
Positive paths remain opaque at Mu and reference constructors.

The actual row prefix derives current resources and store laws. One
ResourceParentWriters.edge_call supplies the historical Written. The
actual accessor and combination supply coherent fixed combined records
and inherited coverage. ResourceParentPositiveBack.children is used once.
PositiveQuotientCount.child_count is used once for the exact selected slot.
The earlier completed walk supplies validity and operation growth at the
real later descent. descend_correct gives its literal payload, including
a cached hit. The proof consumes that equality before reducing wrappers.

Nonplain rows strictly decrease the first component. The proof requires
no mass bound for their changed children. For plain rows, the valid forward
implication gives empty source equalities. Conditional Shape then gives a
proper original child or Empty. Node child mass and positive edge mass
give strict structural decrease, including an Empty returned from a
nullary source row. Weak class count and strict mass give the other branch.

The mandatory 250-line stop occurred before a compiler command. Root and
independent review read the complete draft. The approved private trim
removed one unused growth result, its proof and caller binding. Original
source and exact patch remain. Strict1 failed on a Bool lemma name.
Strict2 failed on unconstrained literal container metadata. Strict3 failed
on unreduced payload wrappers. Strict4 showed that simultaneous simp
unfolded the payload before the supplied equality could match. The final
repair rewrites first and then reduces wrappers. Every full raw diagnostic
and exact patch was reviewed before the next launch. Root read large
repeated contexts through lossless line deduplication with exact byte
reconstruction. Those JSON records add no compiler commands.

Selected strict5 and the separate root strict have literally empty logs.
The sole FULL output has 17758839 bytes, SHA256
0a160c4edf65db46a006736308311716790dcd0c76adadb857ccbd6eecc26bc9.
Printer SHA256 is
d49a8e5b28d026bf9ff6b5b26de0dadda672f510e581d7ae2230e83f317fbe2e.
Complete checked/printed types match: 38645 raw and 22023 non-whitespace
characters. The retained proof has 17680656 characters. All eight settings,
unique actual lambda delimiter, no omissions, no private public TYPE names
and actual propext/Classical.choice/Quot.sound were verified. Six author
commands plus root strict and Audit give eight actual jobs, four failures.
Every launch has fresh usage, effective max/high 4 GiB, zero swap and a
five-minute cap. Independent review contributes zero proof/runtime jobs
and discloses transitive foundation authorship.

The archived 33-line next plan and exact 39-line body_rank_lt proposal
remain source-only evidence. The body proof must first decompose the
actual ordinary-body prefix. It must call dispatch with each hop's own row
and actual cuts. A fresh activation must identify the captured full request
using readiness and the two canonical identity primitives at the same
Context. A strict smaller-fuel induction index can compose the measure;
fuel itself is not the claimed rank. Initial evaluating cells still need
a separate initial-idleness boundary for a global ancestor claim.
No completed outer call, future owner return or supplied chain is assumed.
Finite fresh renewals, completion and Haskell refinement remain separate.
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
(ROOT / 'lean/notes-current-actual-child-rank.md').write_text(note)
print('Updated nine documents and focused note. All prior text remains.')
