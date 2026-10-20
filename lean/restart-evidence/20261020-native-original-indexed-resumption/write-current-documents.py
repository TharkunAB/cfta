import datetime,json
from pathlib import Path
from zoneinfo import ZoneInfo
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
proof=(HERE/'proof-commit.txt').read_text().strip();stats=json.loads((HERE/'attempt-accounting.json').read_text())
stamp=datetime.datetime.now(ZoneInfo('Europe/Stockholm')).strftime('%Y-%m-%d %H:%M %Z')
block=f'''## Current indexed source-row binder resumption

Updated: {stamp}. Proof checkpoint: `{proof[:9]}`.
Verified start: `1c613eabe`. Imported main remains `794903b3f`.
Read `lean/notes-current-native-original-indexed-resumption.md`.

One actual completed original build from empty fixes one publication path.
Each indexed outer writer fixes its actual raw callback before all stored
rows. A joint source-row induction keeps the same terminal call and
original union descent. A node terminal retains its actual RowCall.
A binder terminal keeps its probes, request, complete selected payload,
smart finish and selected stored row. That same full cell reaches only
the enclosing outer.afterBody. The same path then supplies an earlier
writer at index i < j. Its exact event, complete payload, prefix, three
callback paths, physical and issued suffixes remain together. Its actual
raw callback stays fixed before all rows of the selected stored body.
No independent Stored or Observed event is selected or equated.

The same warm source example consumes this producer once. Its own source
route and actual filter force the already-returned terminal to nested.
It removes only that terminal's node alternative. It retains the complete
earlier indexed binder receipt and actual tag17 raw SourceRow. The public
example also retains all generic clauses. It runs no unfold or native
execution prefix and adds no independent source family.

One public and one constructed full readback pass with standard axioms.
Root strict logs are empty. Canonical and default Audit pass: 3538 jobs
and 74334 theorem dependency checks. Only the older ClosedCompletion
warning remains. All {stats['capped_commands']} actual capped Lean/Lake commands and
{stats['failed_commands']} failed attempts remain. Counts do not measure completion.
Every earlier proof, draft, repair and counterexample remains.

The next proof must iterate the same indexed row transition to an actual
original node RowCall. Strong induction on its same publication index is
the proposed route. That endpoint theorem remains unproved here.
Source chronology does not give global native owner-renewal progress.
Generated-capture ancestry, residual observations, active-owner exclusion,
final retention, general outer completion, convergence and production
Haskell refinement remain open. All 268 Haskell and 207 active package
files keep their bytes. FINDINGS retains the external repair registry
first. No new Haskell fix or runtime result is claimed. The full goal
stays active. Pushes to formalize remain authorized.

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
An actual completed original build from empty now fixes one indexed path.
Each indexed outer writer fixes its raw callback before all stored rows.
The same source-row induction derives terminal and union descent jointly.
Its node arm keeps the actual RowCall. Its binder arm keeps the current
probes, request and selected complete payload, then derives an earlier
i < j in that same path. The cell is transported only to outer.afterBody.
The exact earlier event fixes its own raw callback before all stored rows.
No independently existential Stored or Observed writer is selected.
The same warm source forces its already-returned nested terminal and
retains the full earlier receipt and actual tag17 source row. One public
and one constructed full readback pass. Root strict logs are empty.
Default Audit passes: 3538 jobs and 74334 theorem dependency checks.
All {stats['capped_commands']} actual Lean/Lake jobs and {stats['failed_commands']} failed attempts remain.
No new Haskell fix or runtime result is claimed. The imported PR #97
repair and all earlier external fixes remain above or below this update.
The prior read-only formatter checks remain valid for unchanged files.
All 268 Haskell and 207 active package files retain their bytes.
Ultimate original node ancestry remains the next unproved step.
Global renewal, active-owner exclusion, final retention, outer completion,
convergence, generated ancestry, residual observations and Haskell
refinement remain open. Read
`lean/notes-current-native-original-indexed-resumption.md`.
Preserve every external repair, reproducer and validation result below.

'''
(HERE/'findings-update.md').write_text(finding)
path=ROOT/'FINDINGS.md';text=path.read_text();anchor='Current proof update: 2026-10-20 23:03 CEST.';assert text.count(anchor)==1
path.write_text(text.replace(anchor,finding+anchor,1))
note='# Same-trace source rows and strictly earlier binder writers\n\n'+block+f'''## Whole-library target and current claim

For each public operation, valid supported initial inputs must imply
that execution terminates and satisfies the intended specification.
Support must follow from initial data and resources. It must not assume
a future successful result. The target includes construction, transforms,
reduction, size classes, counts, ranks, enumeration, generation,
probability, external interfaces and the optimized interned core.
The older constructor and equality proofs remain in scope.

The model has conditional root-language and exact Sized results under
their stated premises. The new theorem connects stored rows of actual
original source publications to their actual node call or a strictly
earlier binder writer. It derives chronology and row provenance in the
same trace. General native termination and Haskell refinement remain
unproved. There is no reliable completion percentage from proof totals.

## Exact producer

SourceCurrentNativeOriginalIndexedResumption adds one public theorem,
build_row_resumptions. Its only data premise is the actual completed
closed original build from empty. Entry Context and initial absence of
full Mu cells follow from empty. It calls build_trace_writers once.
It retains that same path, indexed rooted sites, final-cell selector and
universal precompletion selector.

For every event in that path, callback_rows fixes the actual raw build,
filter, local Context and original callback Reached before all stored
rows. publication_body_origin derives each row's source at that fixed
callback. Equality of the same actual build aligns the raw results.
There is no equality premise about independently selected writers.

The private joint source-row helper is copied byte-exact from the old
UnionDescent module. It derives the terminal and exact indexed union
route together. It keeps the actual terminal build, Context, original
Reached, generic SyntaxBound and physical/issued suffix to rawAfter.
The original route with no initial inputs excludes capture terminals. The node case
retains distinct source/output indices, canonical lookup and RowCall.
It requires no selected child and therefore covers nullary rows.

The binder case inspects the same SourceRow.binder. It keeps actual
depth and ordinary callbacks, request, selected complete cell, smart
finish equality and RowAt of the selected stored body. The actual raw
return Context proves validity for the same withoutSelfReference filter.
Its growth and issued extension end at outer.afterBody, before outer
completion. The selected full cell moves through that exact suffix.
The same path's precompletion selector supplies an earlier index i < j.
The result keeps that exact earlier event, key/full candidate equality,
missing cell, prefix, three callback paths, original Reached and both
suffixes ending at outer.afterBody.

callback_rows then fixes the raw callback of that exact earlier event.
Full Mu equality identifies its body with the selected stored body.
The result exports the selected literal row's actual raw SourceRow and
all rows of that stored body at this same earlier callback. It does not
call the older existential BinderResume or Stored/Observed interfaces.
Those older theorems remain valid and preserved. No private bookkeeping
predicate occurs in the new public type.

## Concrete nonvacuous consumer

The source is the same box[nested,outer] family. Nested is a raw false
binder over nullary tag17. Outer is a raw false binder over
union[var0,nested]. The original build and full outer record are computed.
One new producer supplies the path and every generic clause.
Its final-cell selector chooses the indexed outer writer.

Finite original Reached paths classify the selected writer's expression.
The actual callback SourceRow and filter exclude the nestedBody case:
its raw node cannot filter to the selected full Mu body. Thus the
selected expression is outerBody. That same returned UnionDescent,
nonunion fact and terminal kind force its already-returned terminal to
nested. Only that terminal's node alternative is removed. Its existing
binder tuple, earlier index/event and fixed earlier raw callback remain.
The concrete tag17 SourceRow and universal earlier stored-row sources
are retained. No manual event or heap identity is assumed. This example
adds no source family, actual unfold or native execution prefix.

## Verification and preservation

Proof authority: {proof}.
Evidence: lean/restart-evidence/20261020-native-original-indexed-resumption/.
One public FULL and one constructed FULL retain complete types, proofs
and axiom reports with all eight printer options. Only propext,
Classical.choice and Quot.sound occur. Root personally observed strict,
canonical, default Audit and independent strict fixture jobs at terminal
exit zero. Strict raw logs are empty. Audit reports 3538 jobs and 74334
theorem dependency checks. Only the older ClosedCompletion warning
remains in canonical dependencies and Audit.

All {stats['capped_commands']} actual capped Lean/Lake commands remain, including
{stats['failed_commands']} failed attempts. Each attempt keeps its source, raw log, receipt,
fresh usage and effective caps. Copies add no jobs. The private binder
core adds no official public pair or auxiliary FULL. Independent complete
source and fixture reviews add no Lean jobs. All heavy checks use 4 GiB
memory max/high, zero swap and five minutes.

Preservation checks 45556 starting files, 3534 older non-Audit Lean
sources, 222 frozen manifests with 1293 entries, 268 Haskell files,
207 active package files, two stashes and three other worktrees.
Audit adds only the declared import. Every earlier proof, counterexample,
repair, draft and evidence file keeps its bytes. Main794903b3f and its
PR #97 documentation repair remain imported. Prior formatter results
remain preserved. No fresh Haskell runtime validation is claimed.

Publication receipts remain outside the sealed checkpoint. Post-push
closure checks every tracked blob and mode against the index and HEAD,
checks all evidence and exact remote formalize, and records remote main
independently. A later main advance does not rewrite the source baseline.

## Next proof and remaining work

Read next-node-plan/plan.md in this evidence directory. It is a pinned
proposal. Strong induction on the same event index should show that each
selected initial-source stored row ultimately comes from an actual
original node RowCall. The node arm ends the induction. The binder arm
carries the same literal row to the earlier body's RowAt using exact
full payload equality. That earlier index is strictly smaller. The next
proof must consume the current producer once and retain that same path.
A generic theorem that assumes all transitions decrease is insufficient.
The actual ultimate-node endpoint is still unproved here.

For actual unfold outputs, retain the exact original stored-row anchor.
Output children can differ. Do not identify the changed output row with
its original row. Node-child descent requires the actual ordered source
child route. These facts do not yet relate all native-generated captures
or residual observations to an initial closed-source trace.

The largest gap remains a valid progress argument across arbitrary
native owner renewal and warm historical winners. Ordinary-height
descent has a checked counterexample. Generated nonempty-capture ancestry,
preceding native histories, residual Mu observations and ordinary
continuations remain open. Global active-owner exclusion, final owner
retention, general outer completion, repeated-pass convergence and
production Haskell refinement remain open. The full goal stays active.
'''
(ROOT/'lean/notes-current-native-original-indexed-resumption.md').write_text(note)
print(json.dumps({'status':'PASS','proof':proof,'updated_existing_documents':9,'new_note':1}))
