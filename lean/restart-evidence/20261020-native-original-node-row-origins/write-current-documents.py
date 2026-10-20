import datetime,json
from pathlib import Path
from zoneinfo import ZoneInfo
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
proof=(HERE/'proof-commit.txt').read_text().strip();stats=json.loads((HERE/'attempt-accounting.json').read_text())
stamp=datetime.datetime.now(ZoneInfo('Europe/Stockholm')).strftime('%Y-%m-%d %H:%M %Z')
block=f'''## Current ultimate original node-row provenance

Updated: {stamp}. Proof checkpoint: `{proof[:9]}`.
Verified start: `d425c2942`. Imported main remains `794903b3f`.
Read `lean/notes-current-native-original-node-row-origins.md`.

Every full structural row stored in an indexed Mu publication of one
actual original build from empty now has an actual original node call.
One indexed-resumption producer fixes the same path for the whole proof.
Strong induction on its publication index eliminates repeated binder
stops. Each binder step carries the complete same row to an earlier
body at i < j. The result retains an indexed producer k <= j, exact
UnionDescent and generic SyntaxBound relative to that producer, original
Context and Reached, actual node SourceRow/build/buildEdges/makeNode,
distinct source/output indices and full RowCall output equality.
Physical and issued suffixes end at the selected outer.afterBody.
No child premise, writer identity or requester-size decrease is assumed.

The same warm source example reaches its actual nullary tag17 node
RowCall. It derives strict k < j in the same returned path. Equal indices
would force equal events by their same list lookup. The actual outer
callback and node UnionDescent exclude that case. No manually selected
creator identity is assumed. All generic node-origin clauses remain.
This example runs no unfold or native execution prefix.

One public and one constructed full readback pass with standard axioms.
Root strict logs are empty. Canonical and default Audit pass: 3539 jobs
and 74335 theorem dependency checks. Only the older ClosedCompletion
warning remains. All {stats['capped_commands']} actual capped Lean/Lake commands and
{stats['failed_commands']} failed attempts remain. Counts do not measure completion.
Every earlier proof, draft, repair and counterexample remains.

The next bridge must connect actual initial captures and successful
unfolds to these original full rows. Preserve the generated-capture arm
and the unfold's original stored-row anchor and actual child Calls.
Changed output children need not equal original stored children.
Global native renewal and active-owner exclusion, final retention,
general outer completion, convergence, generated ancestry, residual
observations and production Haskell refinement remain open.
All 268 Haskell and 207 active package files keep their bytes. FINDINGS
retains the external repair registry first. No new Haskell fix or runtime
result is claimed. The full goal stays active. Pushes remain authorized.

'''
paths=['NEXT-PROMPT.md','HANDOFF.md','lean/README.md','lean/SYSTEM.md','lean/API-COVERAGE.md','lean/COVERAGE.md','lean/notes-proof-status-20261017.md','lean/notes-current-system-claim.md']
for name in paths:
 path=ROOT/name;text=path.read_text()
 if name=='NEXT-PROMPT.md':
  prefix='Continue the cfta formalization in /home/tritlo/Code/mcfta.\n\n';assert text.startswith(prefix);text=prefix+block+text[len(prefix):]
 else:
  first,rest=text.split('\n',1);text=first+'\n\n'+block+rest.lstrip('\n')
 path.write_text(text)
finding=f'''Current proof update: {stamp}. Proof checkpoint: `{proof[:9]}`.
One actual original build now supplies ultimate original node calls for
every full stored row of every indexed Mu in its same publication path.
Strong induction on the same index eliminates repeated binder stops.
The selected complete row is unchanged. The result keeps k <= j, the
same producer lookup, producer-relative bound and union route, original
Context/Reached, actual node SourceRow/build/buildEdges/makeNode,
distinct indices, full RowCall output and both suffixes to outer.afterBody.
The same warm source derives its actual nullary tag17 node call with
strict k < j. Equal-index event equality is derived from the same list
lookup only. No manual creator identity is assumed. One public and one
constructed full readback pass. Root strict logs are empty. Default
Audit passes: 3539 jobs and 74335 theorem dependency checks.
All {stats['capped_commands']} actual Lean/Lake jobs and {stats['failed_commands']} failed attempts remain.
No new Haskell fix or runtime result is claimed. The imported PR #97
repair and all earlier external fixes remain above or below this update.
Prior formatter results remain valid for unchanged source files.
All 268 Haskell and 207 active package files keep their bytes.
Actual initial capture/unfold correspondence is the next bridge.
Global renewal, active-owner exclusion, final retention, outer completion,
convergence, generated ancestry, residual observations and Haskell
refinement remain open. Read
`lean/notes-current-native-original-node-row-origins.md`.
Preserve every external repair, reproducer and validation result below.

'''
(HERE/'findings-update.md').write_text(finding)
path=ROOT/'FINDINGS.md';text=path.read_text();position=text.index('Current proof update:');path.write_text(text[:position]+finding+text[position:])
note='# Ultimate original node calls for stored recursive rows\n\n'+block+f'''## Whole-library target

For each public operation, valid supported initial inputs must imply
that execution terminates and satisfies the intended specification.
Support must follow from initial data and resources. It must not assume
a future successful return. The target includes construction, transforms,
reduction, size classes, counts, ranks, enumeration, generation,
probability, external interfaces and the optimized interned core.
The older constructor and equality proofs remain in scope.

## What is proved now

SourceCurrentNativeOriginalNodeRowOrigins adds one public theorem,
build_node_row_origins. The input is an actual original build from empty
with no initial input values. It calls build_row_resumptions once.
The result retains that same path, indexed rooted sites and final full
cell writer selector. For every indexed publication and every structural
RowAt of its body, it derives an ultimate original node producer for
the complete same EdgeValue, including stored children.

The producer index is at most the selected outer index. Its lookup is
in that same path. Its node expression keeps UnionDescent and the generic
SyntaxBound relative to its own producer expression. The result keeps
Context, original Reached, actual node SourceRow and completed build,
actual buildEdges and makeNode, canonical output lookup and a RowCall
whose output is the complete selected row. Source and output indices
remain distinct. No selected child or positive arity is required.
The physical and issued suffixes end at outer.afterBody.

This closes repeated binder stops for original stored-row provenance.
It does not establish that arbitrary native execution terminates.
The existing conditional root-language and exact Sized results retain
their premises. Production Haskell refinement remains unproved.
There is no reliable completion percentage from declaration totals.

## Actual induction

The proof fixes the common path and all indexed row clauses once.
Strong natural induction on the selected index keeps the event, lookup,
row and RowAt universally quantified. The node arm already supplies the
actual call. Its exact terminal-to-raw suffix composes with the same
actual withoutSelfReference filter to outer.afterBody.

The binder arm supplies a strictly earlier index and exact full candidate
equality. Mu injectivity transfers the complete same row to that earlier
body. The induction hypothesis returns its ultimate node call. Its
producer-relative bound, route, rooted call and complete row stay intact.
Its physical suffix extends through the earlier publication completion
and the retained earlier-to-current suffix. Publication keeps issued
names unchanged, so the issued suffix composes too. No standalone issued
Path is fabricated for completion. No source-size decrease is claimed
across a historical writer jump.

## Nonvacuous actual example

The source stays box[nested,outer]. Nested is a raw false binder over a
nullary tag17 node. Outer is a raw false binder over union[var0,nested].
The example computes the original build and final outer full cell.
One producer fixes the path and every generic node-origin clause.
Its final-cell selector chooses an indexed outer publication.

The actual callback SourceRow and filter, together with finite original
Reached classification, identify that selected expression as outerBody.
The new node-origin clause returns the actual tag17 node call at k <= j.
If k = j, the two same-list lookups force the producer and outer events
to be equal. Its node UnionDescent would then start at outerBody. That
union can stop only at var0 or nested, so this is impossible. Thus k < j.
The proof retains the full returned node SourceRow/build/RowCall and
both suffixes to that same outer.afterBody.

No manual historical event or heap identity is assumed. This is the
same source family as before, with a stronger endpoint theorem. It adds
no independent example and executes no unfold or native prefix.

## Verification and preservation

Proof authority: {proof}.
Evidence: lean/restart-evidence/20261020-native-original-node-row-origins/.
One public FULL and one constructed FULL retain complete types, proofs
and axiom reports with all eight printer settings. Only propext,
Classical.choice and Quot.sound occur. Root personally observed strict,
canonical, default Audit and independent strict fixture checks at terminal
exit zero. Strict raw logs are empty. Audit reports 3539 jobs and 74335
theorem dependency checks. Only the older ClosedCompletion warning
remains in canonical dependencies and Audit.

All {stats['capped_commands']} actual capped Lean/Lake jobs remain, including
{stats['failed_commands']} failed attempts. Each attempt keeps its source, raw log, receipt,
fresh usage and effective caps. Copies add no jobs. Independent complete
source and fixture reviews add no Lean checks. All heavy checks use
4 GiB memory max/high, zero swap and five minutes.

Preservation checks 45847 starting files, 3535 older non-Audit Lean
sources, 223 frozen manifests with 1294 entries, 268 Haskell files,
207 active package files, two stashes and three other worktrees.
Audit adds only the declared import. Every earlier proof, counterexample,
repair, draft and evidence file keeps its bytes. Main794903b3f and its
PR #97 documentation repair remain imported. Prior formatter results
remain preserved. No fresh Haskell runtime validation is claimed.

Publication receipts stay outside the sealed checkpoint. Post-push
closure checks all tracked blobs and modes against the index and HEAD,
all evidence, exact remote formalize and the independently read main.
A later main advance does not rewrite a source baseline.

## Next actual native bridge

Read source-review/next-initial-capture-unfold.md in this evidence folder.
That pinned note is unproved. The next consumer must invoke the lower
actual capture API once and preserve its generated branch. In its initial
cell branch, feed the exact original full cell to this path's final-cell
selector. Do not identify the indexed event with an old opaque Observed
or Stored event. Derive current semantic and causal history from actual
source construction and the actual native trace.

For an actual successful unfold, retain its original storedRow anchor,
exact symbol, guard and arity, and identity or actual ordered child Calls.
Apply ultimate node provenance to that original storedRow. Actual output
children can differ. Do not identify changed output with the stored row,
or derive earlier causal history by reverse growth.

## Remaining major work

The largest gap is still a valid progress argument across arbitrary
native owner renewal and warm historical winners. Ordinary-height
descent has a checked counterexample. Generated nonempty-capture ancestry,
preceding native histories, residual Mu observations and ordinary
continuations remain open. Global active-owner exclusion, final owner
retention, general outer completion, repeated-pass convergence and
production Haskell refinement remain open. The full goal stays active.
'''
(ROOT/'lean/notes-current-native-original-node-row-origins.md').write_text(note)
print(json.dumps({'status':'PASS','proof':proof,'updated_existing_documents':9,'new_note':1}))
