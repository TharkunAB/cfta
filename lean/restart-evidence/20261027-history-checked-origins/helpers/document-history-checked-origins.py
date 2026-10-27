from pathlib import Path
import hashlib,json,re,subprocess
r=Path('/home/tritlo/Code/mcfta');a=Path('/tmp/mcfta-history-checked-origins-20261027')
head=(a/'source-head.txt').read_text().strip();base=(a/'published-base.txt').read_text().strip()
pub=json.loads((a/'public-validation.json').read_text());assert pub['status']=='pass'
raw=(a/'build-audit-final-1/raw.log').read_text();jobs=re.search(r'Build completed successfully \((\d+) jobs\)',raw).group(1);count=re.search(r'Checked axiom dependencies of (\d+) MicroCFTA theorems',raw).group(1)
modules=json.loads((a/'modules.json').read_text());lines=sum(len((r/'lean/MicroCFTA'/f'{m}.lean').read_text().splitlines()) for m in modules)
assert len(modules)==7 and lines==1158 and pub['new_public_theorems']==36
prefix=f'''
## Checked arity origins and actual physical edge-body returns

Source checkpoint: {head}.
Every completed rich native edge-body receipt now derives projected arity
from its actual first instruction, actual child walk and returned constructor.
Initial physical Good and actual edge readiness remain explicit. The receipt
can have any postcondition. No separate ready branch, child semantic result,
arity check or future success is assumed. Both the accepted and sentinel
branches retain their actual full-state endpoints and origin observations.

Checked source syntax now derives an edge-key arity invariant. Actual source
construction and stored reconstruction preserve it, including Mu unfolding,
canonical hits and pending prefixes. Actual checked MkEdge and raw rejection
receipts preserve the ENTIRE edge-record invariant from before to after.
An actual selected head consumes that invariant at its own caller heap.
Existing Parent construction receipts also supply returned-edge arity and
retain it through actual Posts and matching canonical edge identity.

This does not yet derive arity-certified histories from the bare finite
producer. Raw buildEdges does not check arity. SourceChecked explicitly
requires normalized fields and actual successful checks at source counts.
Rejected checked inputs use their actual sentinel return. Current Packet and
physical memo validity do not supply missing checked origins for new records.
Native query, cache, local-reduction, exposure and history propagation remain
open. The previous conditional whole-history original acceptance theorem
and H6 global finite-tree construction theorem retain their full contracts.
Enumeration coverage and physical Haskell correspondence remain open.

Seven modules, {lines} lines, 36 public theorems and eight definitions pass
strict checks. Audit passes {jobs} jobs and {count} dependency checks. Six
previous strongest signatures and axiom sets match byte exactly.
No Haskell source changed. FINDINGS preserves all fixes and repair handoffs.
The whole-system goal stays ACTIVE. Keep the optimized interned core and
all older constructor and equality proofs, drafts, counterexamples and repairs.
Details: `lean/notes-current-checked-arity-origins.md`.

'''
paths=['NEXT-PROMPT.md','HANDOFF.md','FINDINGS.md','lean/API-COVERAGE.md','lean/COVERAGE.md','lean/README.md','lean/SYSTEM.md','lean/notes-current-system-claim.md','lean/notes-proof-status-20261017.md'];records=[]
for name in paths:
 p=r/name;old=p.read_bytes();assert old==subprocess.check_output(['git','show',base+':'+name],cwd=r)
 dst=a/'prior-documents'/name;dst.parent.mkdir(parents=True,exist_ok=True);dst.write_bytes(old)
 first,rest=old.split(b'\n',1);insertion=prefix
 if name=='FINDINGS.md':
  insertion+='''
### Formal constructor boundary and Haskell repair status

No Haskell source or Cabal file changed. All older fixes, regressions and
external repair instructions remain below without change. The integrated
LPO fix and extraction documentation repair remain present. Main remains
8766699b594eaad80381af2eee034c378ccf3192 at the refresh for this checkpoint.
The separate KBO weight candidate d7b6a9dfff464eb32c17c314d4825d5b027f1b2d
is not on main and is not integrated, built or executed here. The earlier
positive-Int context-reversal finding remains open in this branch. Its Natural
and lazy-map repair has only the recorded source assessment. Run the targeted
native regression after the repair lands on main. No runtime success follows
from this Lean-only checkpoint.

The general Lean buildEdges API emits a raw makeEdge with the supplied guard
and actual constructed children. It does not execute the source arity test.
Haskell mkEdge rejects a failed arity check. Normalized guard fields, closure,
residency and a generic native Post do not establish the missing relation
between constraint positions and actual child count. The new SourceChecked
bridge makes original successful source checks explicit. Actual rejected
inputs must use their sentinel return. Do not infer all raw syntax passes.

Current physical memo NodeGood and EdgeGood fields retain availability and
residency. They do not retain checked constructor origins. A returned Parent
edge has a construction receipt, but its live final constructor starts at a
middle state after local reduction. Returned-edge arity plus a generic Post
cannot classify every record created before that middle state. This is a
formalization resource boundary, not a verified Haskell defect. Carry and
derive the actual query and local-reduction resource before removing the
history's arity annotation. Keep all earlier Haskell repair evidence intact.

'''
 data=first+b'\n'+insertion.encode()+rest;p.write_bytes(data)
 records.append(dict(path=name,bytes=len(data),sha256=hashlib.sha256(data).hexdigest(),offset=len(first)+1,inserted_bytes=len(insertion.encode())))
note=f'''# Checked arity origins for actual native construction and reconstruction

Source checkpoint: {head}.
Published base: {base}.
Imported main: 8766699b594eaad80381af2eee034c378ccf3192.
The whole-system goal stays ACTIVE. Keep the optimized interned core.
Preserve all older constructor and equality proofs, drafts, counterexamples
and repairs. Previous checkpoint: `notes-current-history-assignment-rendering.md`.

## Target and strongest statements

The target remains source-connected correctness for the whole CFTA system.
It includes exact finite-tree language preservation, enumeration soundness
and coverage under explicit solver, selector and pruning contracts, plus
correspondence with the physical Haskell implementation. It is incomplete.

H6, SourceCurrentColdFiniteWarmCalls.constructed_node_calls, remains the
strongest global exact finite-tree construction theorem. Covered closed
construction, a valid original guard-allocation history and empty inherited
payload derive width and work fuels for any finite budget and round count.
Actual modeled node calls complete. Their final node stays available and
accepts exactly the original finite trees in every ambient environment.
This does not establish convergence or physical Haskell execution correctness.

The strongest recursive semantic result remains the previous conditional
whole-history theorem. An actual arity-certified ResourceHistory, actual
restart decision, initial Canonical, own-output Discharged, actual successful
native render and checked returned residuals construct an assignment and prove
original stored-root native acceptance with every original suspended Holds
clause. The assignment satisfies original input, own output and rendered state.
No desired original acceptance or final Satisfies is an input. The finite
producer keeps its entire old admission and result. Arity certification remains
an antecedent of the appended acceptance observer, not a producer admission.
This checkpoint does not yet remove that antecedent.

The strongest new local native statement is body_receipt_fits. Given initial
physical Good, the actual EdgeReady request and the SAME completed rich physical
edge-body Receipt, it derives projected arity of the actual returned edge.
The receipt's postcondition is arbitrary. It assumes no ready-prefix result,
accepted branch, child semantic receipt or desired returned arity. The proof
extracts the actual first trace step, actual loads and actual constructor check.
It returns either the accepted raw ordered child Walk and full constructor
endpoint, or the actual sentinel step, remaining Trace, full endpoint and
Top/Empty fields. No raw completion is promoted to a rich receipt as a shortcut.
This certifies the returned row. It does not certify every child-created record
or every output of a whole native query.

## Arity resource and checked source

SourcePruningEnumerationArityOrigins.Fits constraint arity states that every
successful constraint projection refers only to existing root children.
Heap relates each physical edgeRecords key to its own key.children.length.
It checks the whole edge-record table. This is an arity predicate, not an
assignment-satisfaction predicate. Coherent resident payloads derive the same
count from their key, so Heap.edge checks an actual returned edge payload.

Checked source syntax records Fits at each original syntactic child count.
Actual buildMany success retains the number of child plans. The build, child
and row inductions therefore check each actual new key after its real children
complete. Older records survive insertion. Ordinary nodes, unions, filters,
both Mu probes, reservation, canonical hits and pending callbacks retain the
same invariant at their actual stopping heap. No final invariant is an input.

SourceChecked is the more source-specific original condition. Each edge has
Cached equalities and passes SourceEqualityMkEdgeAllocation.accepted at its
original syntactic child count. Fits.of_accepted derives projected arity from
that actual Boolean check, fits_exact and project_complete. The source-checked
induction derives Checked, then the actual closed raw build derives Heap.
This is a genuine explicit original condition. It does not prove arbitrary
raw syntax passes the source test. It does not change raw buildEdges to reject
failed checks. A failed checked source input must use its actual sentinel.
The source guard-allocation and checked-construction connection must remain
explicit when initializing the full recursive producer.

Stored substitution copies each original guard and retains the number of
encoded child plans. Coherent resident records supply the original Fits fact.
Actual encode, ordered child encoding and row encoding therefore derive
Checked for the copied plan. Actual stored execute and cold Mu unfold then
retain Heap through every completed or pending reconstruction prefix.
Environment values do not allocate unchecked edges in this proof.

## Actual checked creation

SourceCurrentAllocatedMkEdge.Receipt.projected_arity derives valid projected
tries and fresh arity directly from the existing checked constructor receipt.
The actual guard and child equations identify accepted fields or the sentinel.
The returned physical context supplies normalized guard fields. RejectReceipt
supplies Top with an empty child. ParentEdge.Receipt.construction already
contains either that rejected receipt or an actual MkEdge receipt after child
reduction. No new arity premise is added to these local receipt consumers.

CompletedHeadReceipt.freshArity_of_parent_construction uses the actual earlier
Parent receipt, returned-heap equation, actual native Post and matching selected
edge identity. Post retains the old resident record. Actual selected residency
and native coherence equate the complete returned edge with that head edge.
Packet alone does not supply the earlier construction witness.

Receipt.preserves_arity_heap and RejectReceipt.preserves_arity_heap preserve
the ENTIRE table from the literal before heap to the literal after heap.
They take only the actual receipt and initial Heap. They invert receipt.actual
to obtain the exact requested makeEdge and returned heap. The final coherent
record supplies its requested key and actual child count. Projected arity of
the returned payload checks that key. The actual insertion keeps every old key.
No extra Ready, desired final Heap or future success is supplied.

A Parent receipt proves arity for its returned edge. In the live branch its
MkEdge receipt starts at a middle state after local child reduction. Full Heap
preservation from the original Parent before-state still needs arity through
that actual reduction. A generic Post or returned-row Fits does not supply it.

CompletedHeadReceipt.freshArity_of_origin_heap consumes Heap at that SAME actual
head caller heap. Original Packet realization gives the literal selected parent
and resident edge. Coherence gives its actual child count. The heap invariant
then supplies the existing numeric head gate. This is a consumer of a derived
resource. It does not assume that every current Packet already contains it.

## Native checked edge bodies

ready_fits derives Fits from the actual allocated ready prefix and normalized
conjoined guard. accepted_body_produced retains the old actual child-walk
admission and the whole old execution, EdgeProduced, Keeps, residency, child
identity and length result, then adds returned-row Fits. The old producer is
called once. Qualification of State names is retained explicitly in the
contract comparison; no new semantic admission is substituted.

accepted_receipt_fits needs initial Good, EdgeReady, actual loads, the actual
ready-prefix observation and the existing SAME rich completed body Receipt.
It extracts the actual raw ordered Walk and full returned state. The actual
Walk.length gives returned width. Final coherence identifies the requested
constructor key. No separate semantic child receipt or middle-state semantic
invariant is needed to check the returned row.

body_choice_checked exposes the real sentinel or ready branch from the actual
yielded first body instruction. body_receipt_fits combines that inversion with
the rich receipt. Missing loads and failed prefixes cannot form this completed
trace. The accepted branch derives the loads and ready result internally.
The sentinel branch uses the ORIGINAL mismatch-provenance receipt at the SAME
supplied DecidableEq instance, then derives the empty projected constraint.
It retains the actual sentinel constructor and complete final checked state.
A temporary duplicate convenience wrapper with a fixed Classical decision
instance was removed. Its earlier passing source remains historical evidence.
The final actual body proof does not replace a supplied runtime instance.

## Remaining work

1. Prove the derived Heap invariant through actual generated native node and
   edge queries, including every child-created record and completed memo cell.
   Existing physical NodeGood/EdgeGood retain availability/residency, not origin.
   Old-record Keeps is insufficient for new records. Use actual child-walk
   executions and their induction resources. Arbitrary generic NativeDemand
   code can request raw unchecked makeEdge; restrict the proof to the actual
   source-generated query programs and their real continuations.
2. Retain Heap through actual local reduction, cold exposure, narrowing and
   every completed head advance, including raw empty rejection paths. The
   reconstruction lemmas cover copied guard/count preservation. They do not
   yet compose the complete actual worker schedule or all stopping endpoints.
3. Thread that resource through the original finite-history producer. Keep
   its entire old admission and result. Append an initial-origin conditional
   resource result that DERIVES arity-certified histories at the same bound and
   actual outputs. Do not merely rename the existing numeric history premise
   or assume future per-step satisfaction. Keep actual inventories/full Memos,
   actual callback caches, metadata and own-output heaps. Entry/recordTypes
   enum frames do not change the native caller, but recursive IH outputs can.
4. Instantiate the previous whole-history acceptance observer with the derived
   history decoration. Initial Canonical, actual discharge/render/residual
   checks and original root lookup stay explicit. Prove coverage separately
   under the real solver, selector, pruning and recursion contracts.
5. Close remaining API and physical Haskell correspondence gaps. The physical
   union-find now uses direct parents/member sets; preserve its representation
   boundary. Keep the original whole-system objective and older proof targets.

## Validation and unsuccessful attempts

Seven modules, {lines} lines, 36 public theorems and eight definitions pass
-DwarningAsError=true -Dlinter.all=true. The aggregate Audit passes {jobs} jobs
and {count} theorem dependency checks. Its standalone strict check passes.
Public readback prints 42 complete theorem signatures/axiom sets and all eight
definitions without elision. All new proofs use only the standard propext,
Classical.choice and Quot.sound axiom set. The six previous strongest full
signature/axiom blocks match byte exactly. Their source files are unchanged.
Heavy jobs run serially with memory.max/high 4 GiB and memory.swap.max 0.
The aggregate replay still reports the pre-existing unused-variable warning
in InternedFreshOrdinaryClosedCompletion. No new linter is suppressed.
No sorry, admit, custom axiom, native_decide or heartbeat override is added.

Preserve all failed and passing variants. The local constructor draft first
failed only on two unused section instances; removing them passed. The shared
heap draft first had ambiguous State imports, then unused simplification and
field-reduction errors, then an explicit nil length goal. Its final version
passes. The constructor-table draft first failed in a private folded-key
lookup simplification; the explicit lookup proof passes. The native draft
retains State qualification, linter and decision-instance corrections. The
unused new sentinel convenience theorem was removed after its own passing
check; all three retained native proof bodies stay unchanged. The all-body
observer first had ambiguous body names, a dependent trace binder and a
sentinel decision-instance mismatch. Its next version needed reflexive load
witnesses after dependent equality substitution. The final version passes.
None of these failed drafts is installed or counted as a successful check.

The portable archive is `restart-evidence/20261027-history-checked-origins`.
The work area is `/tmp/mcfta-history-checked-origins-20261027`.
Use its verifier for compressed originals, source/cut identities, review seals
and document inverses. After committing, use --committed for exact tracked
archive bytes. Freeze the work area and archive after all reviews and checks.
Save later commit/publication receipts outside that area. Never edit any earlier
frozen area or archive. See ROOT-RESUME.json and the archived helper scripts.

## Haskell and upstream

No Haskell source or Cabal file changed. Native tests were not repeated for
Lean-only changes. FINDINGS retains all earlier fixes and repair handoffs.
The LPO fix, extraction documentation repair and earlier Specftacular work
remain integrated. Main remains 8766699b594eaad80381af2eee034c378ccf3192 at the
refresh. KBO candidate d7b6a9dfff464eb32c17c314d4825d5b027f1b2d remains on a
separate branch. It is not integrated, built or executed here. The previous
positive-Int context-reversal finding remains open in the current branch.
The Natural/lazy-map candidate has only the prior source assessment. Run the
exact native regression after it lands on main. No new Haskell defect follows
from the raw-versus-checked Lean constructor boundary described above.
'''
name='lean/notes-current-checked-arity-origins.md';p=r/name;assert not p.exists();data=note.encode();p.write_bytes(data);paths.append(name)
records.append(dict(path=name,bytes=len(data),sha256=hashlib.sha256(data).hexdigest()))
(a/'document-paths.json').write_text(json.dumps(paths,indent=2)+'\n');(a/'document-validation.json').write_text(json.dumps(records,indent=2)+'\n')
print(json.dumps({'documents':len(paths),'proof_lines':lines,'audit_jobs':jobs,'dependencies':count,'source_head':head}))
