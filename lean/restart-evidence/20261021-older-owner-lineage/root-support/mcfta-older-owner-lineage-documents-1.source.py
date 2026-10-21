import datetime
import hashlib
import json
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
start = (HERE / 'starting-head.txt').read_text().strip()
proof = (HERE / 'proof-commit-lineage.txt').read_text().strip()
now = datetime.datetime.now().astimezone().strftime('%Y-%m-%d %H:%M %Z')
assert hashlib.sha256((ROOT / 'lean/MicroCFTA/SourceCurrentOlderOwnerLineage.lean').read_bytes()).hexdigest() == 'd6653bb67934bf1158124417013738b679735c49c057381510909052ca6cd41e'
assert not (HERE / 'lineage-strict-1.log').read_bytes()
audit = (HERE / 'audit-1.log').read_text()
assert 'Build completed successfully (3609 jobs)' in audit and '75056 MicroCFTA theorems' in audit
assert {v['path'] for v in json.loads((HERE / 'components.json').read_text())} == {'lineage', 'independent-review', 'busy-plan'}
full = (HERE / 'lineage/older-owner-lineage-public-1.log').read_bytes()
assert len(full) == 4762369 and hashlib.sha256(full).hexdigest() == 'bfa947fb9c026f6ad1d85f1318a4d597792842705bf6a13f2105fb8f10babfab'
update = f'''## Current request measure decreases through every actual body prefix

Updated: {now}. Proof checkpoint: `{proof[:10]}`.
Start: `{start[:10]}`. Imported main remains `794903b3f`.
Read `lean/notes-current-older-owner-lineage.md`.

OlderOwnerLineage.body_rank_lt now composes the checked child decrease.
A node request reached inside an earlier entered body has strictly smaller
inherited positive-class count followed by structural mass than that
body's complete request. Both actual prefixes remain explicit: initial
phase to body entry, then that body to the candidate node. Genuine initial
resources, native laws, Merge laws and resource writer Origins remain.
No desired activation chain, future return or rank premise is supplied.

The literal prefix derives its ordinary body and same source row. Each
induction step uses that hop's own row membership and actual Parent,
inherited prefix, earlier walk and selected child. ActualChildRank.dispatch
gives the direct decrease. On a fresh activation, the current Context,
readiness, canonical identity primitives and literal unchanged checked
state identify the full captured request with the dispatched request.
The remaining actual body prefix then composes by strict lexicographic
transitivity. Smaller body fuel is only an induction index, not the rank.

This closes the older-body composition target. The next busy-fault consumer
must derive that each evaluating cell belongs to an activation in this
run. Initial node-cache idleness is essential for that ancestry boundary.
Existing InitialBusy.busy already derives the same full fault request.
Combining it with ancestry and this theorem is a separate next proof.
Finite fresh renewal bounds, final retention, outer completion, convergence,
broader initial resources and Haskell refinement remain open. This theorem
does not establish successful completion or whole-library termination.

Strict, complete FULL, independent review and Audit pass. Audit has
3609 jobs /75056 dependencies. Five actual Lean/Lake commands retain one
failed strict with five diagnostics and no warnings. The two-site repair
uses explicit Lex constructor cases and unfolds NodeReady for the same
checked-state equality. The sole 39-line public header stays unchanged.
Selected/root strict logs are empty. Whole checked/printed type identity,
all eight printer settings and actual standard three axioms pass. Original
166-line prelaunch sources and the zero-job Nat.le_trans patch remain.
Final source has 172 lines. Every failed input, raw log and patch remains.
No canonical, infrastructure, constructed, runtime or reviewer proof job
ran. Only the old Audit warning remains. Counts are not completion.

All older proof/evidence bytes and version exceptions remain. Haskell,
packages, imported main, stashes and other worktrees stay unchanged.
No new Haskell defect or repair. FINDINGS keeps its external repair index
FIRST. Work continues as requested.
'''
findings = f'''Current proof update: {now}. Proof checkpoint: `{proof[:10]}`.
The inherited positive-class count and structural mass now strictly
decrease from an actual entered body to any node reached inside it.
Each hop uses its own row and actual receipts. Full captured-request
identity follows from the same current Context and canonical stores.
Fuel is only the private induction index. No future return is assumed.

Strict/FULL/independent review/Audit pass: 3609 jobs /75056 dependencies.
Five actual commands retain one failed strict, its complete five-error raw
log and exact two-site repair. There are no new-source warnings. The exact
39-line header, all eight settings, whole type identity and standard axioms
pass. Original sources and the zero-job prelaunch patch remain. No canonical,
infrastructure, constructed, runtime or reviewer proof job ran.
The separate all-node-busy consumer needs initial node-idleness and the
existing ancestry producer. Finite renewals, retention, completion,
convergence, broader initial resources and Haskell refinement remain open.
This is not a successful-completion or whole-library termination theorem.
No Haskell source, runtime result or external repair changes.
Read `lean/notes-current-older-owner-lineage.md`.
The external Haskell repair index stays FIRST. Counts are not completion.
'''
note = '# Strict request decrease inside an actual older body\n\n' + update + '''
The sole public theorem is SourceCurrentOlderOwnerLineage.body_rank_lt.
Its final source has 172 lines and SHA256
d6653bb67934bf1158124417013738b679735c49c057381510909052ca6cd41e.
Its declaration matches the old 39-line proposal byte for byte, SHA256
029a76efa31ebf7d39d357555267b91b95e626cc409a09c35cfaa203f5b75ecb.
The actual public output checks that previously unelaborated proposal.

The measure is (PositiveQuotientCount.count inheritedRecords value,
InternedValueMass.value value), ordered by Prod.Lex Nat.lt Nat.lt.
No ordinary-body premise is supplied. The actual first Step proves it.
Terminal Empty, union, reference and Mu bodies cannot take an outer node
Step. A zero-fuel ordinary body also cannot supply body_rows.

OuterOwnerPrefix.first_child decomposes the literal body prefix. It gives
the same original row, Parent, live inherited prefix, earlier-slot walk,
exact selected child and direct-or-activation alternative. The proof
derives row membership from that owner's literal row split. One dispatch
call gives the child Reached prefix and strict rank. The direct branch
identifies the candidate with that child. The activation branch retains
the actual captured request rather than replacing it from key equality.

OuterInitialPrefix.reached supplies the actual current Context and input
readiness at that child. AllocatedPartialCallSteps.node_start supplies the
captured full request's readiness and key. beginNode_components preserves
the checked state. At the same Context, ready_eq_of_identity identifies
the inherited value and resident_reference_injective identifies the full
node value. These two facts identify the complete captured request.
No all-cell Good conversion or extra ledger induction is needed.

A private six-phase fuel projection is nonincreasing through all eight
Step constructors. On the extracted body-to-row cut, childFuel+slot+2 is
at most ownerFuel. Thus childFuel is strictly smaller. The induction
hypothesis applies to the exact remaining body prefix, with the actual
activation appended to its global past. Full request equality aligns its
endpoint. Explicit Lex transitivity then composes the proved decreases.

The complete first draft166/99b0 and the prelaunch166/023de remain.
Independent review requested the explicit Nat.le_trans spelling before
any launch. Its exact one-line patch adds zero jobs. Strict1 then failed
with four Lex automation errors and one NodeReady unfolding error. Its
entire 1288-byte raw log and exact two-site repair were reviewed before
strict2. The mathematical contract, current states and public header stay
unchanged. Selected strict2 and root strict have literally empty logs.

The sole FULL output has 4762369 bytes, SHA256
bfa947fb9c026f6ad1d85f1318a4d597792842705bf6a13f2105fb8f10babfab.
Complete checked/printed types match: 19059 raw and 12727 non-whitespace
characters. The retained proof has 4723878 characters. All eight settings,
the unique actual lambda delimiter, no omissions, no private public TYPE
names and actual propext/Classical.choice/Quot.sound were verified.
Three author commands plus root strict and Audit give five actual jobs,
one failure. Every launch has fresh usage, effective max/high 4 GiB,
zero swap and a five-minute cap. Independent review adds zero proof jobs
and discloses transitive foundation authorship. Copied earlier dependency
receipts add no commands to this checkpoint.

The next archived plan proposes OlderOwnerBusy.no_node_busy. It preserves
the genuine initial resource packet and adds explicit initial node-cache
idleness. Existing InitialBusy.busy already identifies the complete same
request at a busy fault. Reached.owners derives its actual enclosing
activation and unfinished body prefix. This theorem would give strict
self-decrease, a contradiction. That consumer is separate here. A cache
that already contains an evaluating cell need not have an activation in
this run. Context alone does not imply initial idleness. Warm suspended
or returned node cells can still satisfy the proposed initial boundary.
Existing edge-idle results concern edge-busy faults separately.
Neither node-busy exclusion nor this composition bounds fresh renewals or
proves fuel-independent successful completion. Haskell refinement remains.
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
(ROOT / 'lean/notes-current-older-owner-lineage.md').write_text(note)
print('Updated nine documents and focused note. All prior text remains.')
