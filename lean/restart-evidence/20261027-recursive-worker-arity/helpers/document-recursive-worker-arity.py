from pathlib import Path
import hashlib,json,re,subprocess
root=Path('/home/tritlo/Code/mcfta');area=Path('/tmp/mcfta-recursive-worker-arity-20261027')
head=(area/'source-head.txt').read_text().strip();base=(area/'published-base.txt').read_text().strip()
public=json.loads((area/'public-validation.json').read_text());stats=json.loads((area/'source-statistics.json').read_text());assert public['status']=='pass';assert json.loads((area/'source-validation.json').read_text())['status']=='pass'
refresh=json.loads((area/'final-upstream-refresh.json').read_text());assert refresh['fetch_exit']==0 and refresh['main_is_ancestor'];main=refresh['main']
audit=(area/'audit-final-1/raw.log').read_text();jobs=int(re.search(r'Build completed successfully \((\d+) jobs\)',audit)[1]);deps=int(re.search(r'Checked axiom dependencies of (\d+) MicroCFTA',audit)[1])
prefix=f'''
## Arity through the recursive worker and captured native heads

Source checkpoint: {head}.
All eight completed recursive partial-worker families now retain arity for
the entire actual returned native heap. The literal worker wrappers retain
every old admission, actual result, Checks, Post, full memo state and language
law. They add only a genuine initial arity heap and its derived returned heap.
The proof follows the actual mutual read graph. It assumes no future child
arity or desired final invariant. Busy, failed and exhausted worker calls
without a completed actual graph remain outside this result.

The proof also retains arity through actual narrowing, selected prefixes,
incoming queries, dispatch, terminal processing, ordered child traversal,
selected edges and captured native heads. Every later child uses the actual
caller and full memo state returned by the previous child. Empty-result
rejection retains its actual reached heap. The captured-slot write changes
only the enumeration cache. Every extended resource producer retains its
entire original result and forecast at that same actual endpoint.

A stronger finite-driver contract now records the aggregate reached heap,
even when outputs are empty, and each emitted output's own heap. Its literal
zero-depth case is proved. Positive recursive depth and the complete
ResourceHistoryWithArity derivation remain open. An earlier recursive
callback can return no outputs and still change the caller used by a later
sibling. The induction must retain that endpoint, all old resources, all
emitted output heaps and the histories at the SAME chosen work bound.
H6 and the conditional whole-history semantic theorem keep their full
previous scopes. Coverage, API contracts and physical Haskell correspondence
remain open. The full formalization goal stays ACTIVE.

Twenty modules contain {stats['lines']} lines and {stats['new_public_theorems']} new public theorems. All pass
strict checks. Audit passes {jobs} jobs and checks {deps} theorem dependencies.
Public readback has {public['theorem_signatures_and_axiom_checks']} complete signatures and axiom sets with no elision.
All {stats['prior_public_theorems']} prior blocks match byte exactly. Two new predicate definitions are
printed in full. Only the three standard Lean axioms occur. No Haskell source
changed. FINDINGS retains every repair handoff. Details:
`lean/notes-current-recursive-worker-arity.md`.

'''
extra=f'''
### Recursive worker arity and Haskell repair status

This checkpoint changes Lean proofs only. All earlier Haskell fixes,
regressions and external repair instructions remain below without deletion.
The successful upstream refresh reads main at
{main}. It is an ancestor of this checkpoint.
The LPO fix and extraction documentation fixes remain integrated. The
separate KBO candidate d7b6a9dfff464eb32c17c314d4825d5b027f1b2d remains
unintegrated, unbuilt and unexecuted here. The positive-Int context-reversal
finding remains open. Run the recorded native regression after its repair
reaches main. Retain the prior source assessment and all field-pool findings.

The new Lean proofs establish completed worker and immediate captured-head
arity preservation. They do not establish a new Haskell defect, a native
regression success, positive-depth driver arity, convergence or complete
implementation correspondence. No Haskell test or benchmark ran in this
checkpoint. All strict checks and builds are Lean checks.

'''
note=f'''# Arity through the recursive worker and captured native heads

Source checkpoint: {head}.
Published base: {base}.
Imported main: {main}.
The final successful fetch confirms that main is an ancestor.
The whole CFTA formalization goal stays ACTIVE. Preserve the optimized
interned core, all older constructor and equality proofs, marked drafts,
counterexamples and repairs. Previous note: `notes-current-worker-arity.md`.

## Target and strongest semantic statements

The target remains correctness of the whole CFTA system. It includes exact
finite-tree transformation laws, enumeration soundness and coverage under
explicit solver, selector and pruning contracts, and physical Haskell
correspondence. This target remains incomplete.

H6, SourceCurrentColdFiniteWarmCalls.constructed_node_calls, remains the
strongest global exact finite-tree construction theorem. A covered closed
construction, original guard-allocation history and empty inherited payload
derive an actual finite call trace for any chosen finite number of rounds.
The theorem supplies sufficient mathematical width and fuel. Every actual
node call completes. The final value accepts exactly the original finite
trees at every ambient environment. It does not assert convergence or cover
withoutRedundantEdges. It does not verify all Haskell execution.

The existing recursive semantic theorem retains its entire contract. An
actual arity-certified ResourceHistory, actual restart decision, initial
Canonical, own-output Discharged, successful native rendering, checked
returned residuals and original stored-root lookup construct an assignment.
The term belongs to the original native value and satisfies every original
suspended Holds clause. The assignment satisfies the original input, own
output and rendered state. Desired original acceptance and final Satisfies
are not inputs. The original finite producer retains every admission and
result field. Its arity-certified history observer remains an antecedent.

The earlier all-outcome native-query theorem remains unchanged. Initial
physical Good, genuine initial ArityOrigins.Heap and the actual InputsThrough
plan imply Heap at every finite native node or edge query outcome. This
includes yielded, done, failed, constraintError and blocked states. It does
not prove arity for every busy or failed recursive worker prefix.

## Completed recursive worker

PartialActualArity follows all eight existing mutual source-read families:
NodeCall, NodeBody, EdgeCall, EdgeBody, Rows, Descendants, Children and Walk.
Each theorem retains the original Context, actual Checks, inherited-ready
and available or resident inputs. It adds initial ArityOrigins.Heap. The
mutual induction derives the heap at every actual intermediate endpoint.
Existing PartialActual is used for physical Context, full memo validity,
availability and residency. It does not supply the new heap invariant.

Parent construction uses the preceding actual local-reduction proof at its
real reached heap. Ordinary raw reconstruction uses the original resident
key, actual child-count equality and coherence at that endpoint. A binder
uses actual_rebuild through Ready, probes and its resident original value.
Prefix and descent allocation retain their literal native heap. Begin,
finish and checked-state advance retain their actual heaps. Rows and Walk
pass the actual earlier Post and full memo state to each later call.

PartialWorkerArity extends all eight original literal verified interfaces.
Every original argument and result field remains. Each wrapper calls its
original theorem once. It retains the exact actual result, complete Checks,
Post, full Memos, availability or residency and language law. It derives the
last Heap field from that same completed actual graph. These are completed
worker observers. They do not prove that every requested worker call will
complete. Busy, failed and exhausted calls without the old completed graph
are outside this statement.

## Actual enumeration resource paths

NativeNarrowArity proves the heap at actual narrowAt, outer narrow, prepare
and advanced prepare results. Actual cold exposure provides the needed
heap before narrowing. Node construction does not create an edge record.
Skip, absent and failed cases retain their actual reached state. PrefixArity
uses the same actual PrefixValid observation. PendingRealized and the real
stored lookup supply availability at that state. It assumes no later heap.

IncomingQueryArity retains the full original resource completion and generic
width completion. Its raw-done observer aligns the same actual native and
phase endpoint through completed uniqueness. IncomingNodeArity retains the
full original generic-width resource producer. IncomingNodeObservedArity,
DispatchArity, FoldArity and TerminalArity retain the original actual
outer-ok resource observations. They cover None, empty raw results and the
original diagnostic branches allowed by those observations. They do not
claim a result for every outer error. Each state-changing path uses the
new query theorem at its own actual caller. The singleton fold passes the
actual Post, full Memos, suffix bounds and derived Heap to its induction.
Terminal processing aligns the actual folded core before its incoming query.

ChildObservedArity follows the literal child dispatch. Terminal partition
uses the original reservation. Shallow cases retain the original caller.
ChildResourcesArity retains every old fragment, query, native, enumeration,
waiting, reference, history and resource field. TraversalResourcesArity
passes the actual returned caller, cache and full Memos to the suffix.
A rejected child returns no fragments and retains its reached native heap.
It advances only the original numerical and annotation forecast for the
unused suffix. It does not replace the actual caller with the initial one.

SelectedEdgeResourcesArity retains both full old selected-edge interfaces.
The actual ordered child buckets include inherited and fresh own-class
entries. Their original reservation covers the traversal. Residual updates
retain the native caller. CapturedEdgeResourcesArity retains both full old
captured-slot interfaces. The final write updates only the enumeration cache.
NativeHeadResourcesArity retains the complete immediate head receipt for
supported, unsupported and arity-rejected alternatives. NativeHeadBoundedResourcesArity retains its full original HeadCacheBounds too. These heads
precede the recursive callback. They do not assert arity at the later
post-callback aggregate caller.

OrdinaryHistoryReceipt.with_arity_from_scan_heap decorates one existing
ordinary receipt from the genuine heap at its original scan caller. The
entered Packet, aggregate Post and completed source receipt identify the
same captured old edge at its actual child count. Initial Heap therefore
derives the required Fits. No heap at a later head endpoint is assumed.
This is a local receipt result. It does not decorate an entire history.

Heap checks each canonical edge-record key at its actual child count.
Fits says that successful constraint projections refer only to existing
root children. An unsupported projection retains its original conditional
meaning. The new proofs do not strengthen it without a projection witness.
Original SemanticReady, inventory, costs, ranges, full memo validity,
selection and finite reservation assumptions remain where required.
Initial Heap must come from genuine checked origins. Closure, raw buildEdges
and memo validity alone do not replace that input.

## Recursive contract and main remaining gap

OutcomeResourcesWithArity retains the same reached caller, inventory and
full Memos witness as the original outcome resources. It adds Heap at that
aggregate endpoint and each emitted output's own caller. A complete result
with outputs=[] still retains its actual returned caller. A stopped result
with a present endpoint aligns that same caller and queries. An absent
endpoint remains absent. Its retained resource witness does not assert an
observable endpoint where the run supplies none. The forget theorem removes
only the arity fields and retains the original witness.

CompleteWithArity retains the old finite-driver universal admission order.
It adds only initial Heap as the last input. It retains the original stable
run and OutcomeResources, then appends the stronger same-outcome receipt.
The exact zero-depth resume and run cases are proved. There is no theorem
from CompleteWithArity to unconditional old Complete: old Complete also
admits inputs without initial Heap. Use the independently proved old finite
completion where that universal contract is required.

Positive recursive depth remains open. An earlier callback can return []
and still change the caller used by the next captured sibling. The chosen
output's ResourceHistory has no tail for that discarded callback. Induction
on chosen output histories alone cannot recover its aggregate heap. The
stronger induction must preserve the whole actual endpoint, every emitted
output heap, every old resource field and ResourceHistoryWithArity at the
same common bound and actual own-output state. Enum-only captured-cache
restores retain the native caller. Post or Keeps alone does not establish
Heap for newly created records. Do not assume a future successful callback,
future Heap, final acceptance or desired final Satisfies to close this gap.

The next sequence is the positive-depth callback, actual finite head,
ordered captured scan, parked and ordinary expansion, then the whole finite
history producer. Align actual stable outcomes at their original common
bounds. Do not replace a low-fuel failure with a hypothetical later success.
Keep all original admissions and complete result packets. Whole enumeration
coverage, remaining API contracts and physical Haskell correspondence remain
separate open goals. No defensible percentage or completion date is claimed.

## Validation and retained attempts

Twenty modules contain {stats['lines']} lines and {stats['new_public_theorems']} new public theorems. All twenty and
standalone Audit pass -DwarningAsError=true -Dlinter.all=true. Aggregate Audit
passes {jobs} jobs and checks {deps} theorem dependencies. Public readback
has {public['theorem_signatures_and_axiom_checks']} full signature and axiom blocks: {stats['new_public_theorems']} new and all {stats['prior_public_theorems']} prior public
blocks. All prior blocks match byte exactly. The {stats['unchanged_prior_sources']} pinned prior source
modules retain their published bytes. Only propext, Classical.choice and
Quot.sound occur. Both new public predicate definitions are printed in full.
There is no sorry, admit tactic, custom axiom, native_decide, heartbeat
increase or linter suppression. New standalone strict logs are empty.
The existing dependency warning about InternedFreshOrdinaryClosedCompletion
is retained in aggregate build logs. It is not hidden or changed.

All draft variants and actual failed checks remain in the evidence. The
Step first check found unused section equality instances. The final helpers
remove those unused instances. The Actual first check found two unnecessary
omit commands; the final source moves two instance-free helpers before the
section and removes the commands. Narrow first checking needed explicit
state simplification for skipped typed cases. Incoming Query preserves its
resource, generic-width and actual-done draft stages and checks. NativeHead's
first check found the old equality section declarations omitted from the
draft. The final source restores those original instances. Bounded receives
the same original declarations before its first successful check. No proof
premise is added beyond the specified initial Heap. Unchecked alternative
Narrow and superseded drafts remain marked as such. They are not results.

No Haskell source, Cabal file, native test or benchmark changes in this
checkpoint. FINDINGS retains all earlier repair instructions. The LPO fix
and extraction documentation fixes remain integrated. The separate KBO
candidate d7b6a9dfff464eb32c17c314d4825d5b027f1b2d remains unintegrated,
unbuilt and unexecuted here. The positive-Int context-reversal finding stays
open. Run its recorded native regression when the repair reaches main.

Portable evidence: `restart-evidence/20261027-recursive-worker-arity/`.
Raw logs and large payloads use deterministic gzip where needed. The
manifest records stored bytes. decoded-files.json records original bytes.
The snapshot retains drafts, actual failed and successful checks, full public
readback, literal contract comparisons, exact source cuts, review receipts
and status-document preservation checks. Run its verify-evidence.py with the
snapshot path and --repository pointing to this checkout. After publication,
--committed also checks that all payloads match Git. Reviews record their
actual read scope. They do not imply a new whole-file review of every import.
The source checkpoint precedes this documentation and evidence commit.
The full objective remains ACTIVE after publication.
'''
# Keep every byte of each prior status document after its first title line.
paths=json.loads(Path('/tmp/mcfta-worker-arity-20261027/document-paths.json').read_text())[:-1]
newnote='lean/notes-current-recursive-worker-arity.md';paths.append(newnote)
records=[]
for name in paths[:-1]:
 p=root/name;old=p.read_bytes();assert old==subprocess.check_output(['git','show',base+':'+name],cwd=root)
 saved=area/'prior-documents'/name;saved.parent.mkdir(parents=True,exist_ok=True);saved.write_bytes(old)
 offset=old.index(b'\n')+1;addition=(prefix+(extra if name=='FINDINGS.md' else '')).encode();new=old[:offset]+addition+old[offset:];p.write_bytes(new)
 assert new[:offset]+new[offset+len(addition):]==old
 records.append({'path':name,'bytes':len(new),'sha256':hashlib.sha256(new).hexdigest(),'offset':offset,'inserted_bytes':len(addition)})
p=root/newnote;assert not p.exists();p.write_text(note);data=p.read_bytes();records.append({'path':newnote,'bytes':len(data),'sha256':hashlib.sha256(data).hexdigest()})
(area/'document-paths.json').write_text(json.dumps(paths,indent=2)+'\n');(area/'document-validation.json').write_text(json.dumps(records,indent=2)+'\n');print(json.dumps({'documents':len(paths),'note_bytes':len(data),'prior_documents_preserved':len(paths)-1}))
