from pathlib import Path
from datetime import datetime
from zoneinfo import ZoneInfo
import hashlib,json
A=Path('/tmp/mcfta-history-checked-origins-20261027');O=A/'history-origin-transport-review';R=Path('/home/tritlo/Code/mcfta')
def sha(d):return hashlib.sha256(d).hexdigest()
def save(rel,d):
 p=O/rel;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(d);return {'snapshot':str(p),'bytes':len(d),'sha256':sha(d)}
def put(rel,x):return save(rel,(json.dumps(x,indent=2)+'\n').encode())
assert not (O/'FROZEN').exists();sources=[]
def cap(p,scope,spans):
 p=Path(p);d=p.read_bytes();r={'source':str(p),**save('source-snapshots/'+p.name,d),'scope':'whole source identity; exact inspected extent separately stated','reviewed_scope':scope,'cuts':[]};sources.append(r)
 for first,last,purpose in spans:
  cut=b''.join(d.splitlines(keepends=True)[first-1:last]);assert cut
  r['cuts'].append({'first_line':first,'last_line':last,**save(f'literal-cuts/{p.stem}-{first}-{last}.txt',cut),'scope':'literal cut','purpose':purpose})
 return d
own=cap(O/'drafts/v1/SourcePruningEnumerationAllocatedOriginHeap.lean','WHOLE110line newly authored initial uncompiled draft reviewed',[(1,22,'scope/imports'),(24,51,'actual makeEdge record and entire table preservation helper'),(53,86,'actual checked receipt inversion and whole Heap output'),(88,108,'actual raw-rejection constructor Heap output')]);assert sha(own)=='8798bb94c3b1ca0fffa0c84fa13fcacf5e2bfedba6bf3b256f5df41fa026083b'
cap(A/'arity-origin-review/revisions/v2.lean','WHOLE191line checked constructor/Parent origin arity source reviewed in preceding bounded source task',[(23,73,'real constructor receipt derives valid actual projection and arbitrary-start arity'),(75,92,'real rejection derives empty projection'),(103,120,'actual Parent construction branch proof')])
shared=cap(A/'origin-propagation-review/drafts/v5/SourcePruningEnumerationArityOrigins.lean','WHOLE v2 read; final v5 reviewed by exact local elaboration-only diff; used signatures unchanged',[(23,43,'key-dependent Fits/Heap and coherent payload extraction'),(68,86,'actual raw makeEdge and node table preservation'),(235,246,'checked original construction theorem'),(314,331,'actual stored reconstruction and unfolding preserves stopping heaps')])
for rel,scope,spans in [
 ('SourceCurrentAllocatedMkEdge.lean','WHOLE217line actual runtime/receipt/finite constructors read',[(35,80,'actual build/reject/receipt fields'),(109,150,'existing actual checked constructor producer'),(163,177,'existing raw reject producer')]),
 ('SourceEqualityMkEdgeAllocation.lean','WHOLE150line raw checked allocation control and actual build read',[(38,47,'real checked accessor control'),(102,115,'literal selected raw makeEdge/error branch'),(117,134,'existing valid source receipt')]),
 ('InternedConstructorTemplates.lean','Focused actual cache/run definitions only',[(92,103,'actual keepFirst edge/node insertion'),(121,142,'literal run and actual edge record correctness'),(228,236,'raw exact makeEdge request')]),
 ('InternedRecordCoherence.lean','Focused canonical key/payload fields and record classification only',[(13,35,'coherent guard/key/count relations'),(65,76,'actual old-or-new record cases')]),
 ('SourceCurrentAllocatedParentEdge.lean','WHOLE210line actual parent runtime/receipt/finite producer read',[(34,46,'actual reduction then final checked construction'),(77,100,'retained construction without entire reduction trace'),(174,197,'actual middle reduction and constructor receipts')]),
 ('SourcePruningEnumerationFiniteHistoryContract.lean','WHOLE original history/contract source read',[(32,65,'full original admission and ordinary local receipt'),(91,125,'same actual parked/ordinary resources/native endpoints'),(164,193,'old CompleteWithHistory chosen bound before all outputs')]),
 ('SourcePruningEnumerationResourceHistoryMeaning.lean','Focused existing numeric arity/history forget/sound contract; full source reviewed preceding checkpoint',[(31,54,'existing complete ordinary receipt plus numeric annotation'),(55,121,'all exact actual history tags'),(123,179,'same-endpoint forget and backward assignment contract')]),
 ('SourcePruningEnumerationFiniteCallbackHistory.lean','Focused full old callback header/result and common-bound proof only',[(38,85,'entire unchanged callback admission and full actual history family'),(111,137,'smaller-depth caller/full Memos/cache and summed common fuel')]),
 ('SourcePruningEnumerationFiniteSiblingHistory.lean','Focused rich invocation certificate only',[(42,80,'actual head input Post/full Memos/kept captured cache and false tail')]),
 ('SourceCurrentAllocatedPartialInvariant.lean','Focused current Context/Post/exact composition only',[(24,45,'Context/Post includes guard annotations and old growth but no child-count arity'),(66,76,'actual native Post composition')]),
 ('SourceCurrentAllocatedNativePhysicalCompletion.lean','Focused actual physical step invariants only',[(128,142,'actual checked step preserves existing fields not new key count')]),
 ('SourcePruningEnumerationRecursiveCallbackCanonical.lean','WHOLE callback actual unchanged caller/metadata/frame source read',[(34,60,'same native heap and exact callback frame; no Heap-from-Frame inference')])
]:cap(R/'lean/MicroCFTA'/rel,scope,spans)
now=datetime.now(ZoneInfo('Europe/Stockholm')).isoformat()
plan='''Smallest actual history transport route

1. Use ArityOrigins.Heap as an additional source-derived KEY-DEPENDENT heap resource, not the existing guard-only Heap. Checked initial syntax plus the actual raw initial build derive it. Existing Context/Good/normalized guards alone do not derive this property. The shared Heap.edge theorem requires actual residency AND current coherence to turn the key child count into payload child count.

2. The proposed AllocatedOriginHeap adds two real creation preservation lemmas. Actual MkEdge Receipt and RejectReceipt plus initial Heap imply ENTIRE actual returned Heap. Invert receipt.actual once. Error cannot match that actual successful constructor receipt; its two real Bool branches choose the exact raw makeEdge. The after receipt supplies coherent requested record fields; its projected_arity theorem supplies Fits of the ACTUAL returned guard/count. Identifying those with the requested key lets shared edge_heap preserve every old record and check every actual newly inserted key, including canonical hits. No final Heap, desired semantic law or future successful action is an input.

3. Parent.final construction is now small but DOES NOT by itself prove Parent preservation from the original before heap. Decompose actual Parent.Edge.live / receipt.construction. Its final MkEdge.Receipt starts at the actual local-reduction MIDDLE. The new lemma applies to Heap at that middle. Derive that fact by actual LocalReduction/child-query preservation, not by generic Post or a universal supplied future-middle invariant. The raw rejected Parent branch applies RejectReceipt directly to original-before Heap. Do not add a redundant Parent-only parallel history schema.

4. Native query/emptiness/cold exposure are the remaining creation boundaries. Shared raw build/encode/execute/unfold theorems cover actual copied guards with unchanged child-plan length. Arity's native accepted-body/sentinel receipts cover concrete returned edges from actual checked child Walk. Lift these through the actual SourceEqualityNativeDemand step/control continuation, optional binders and stopping prefixes. Use current rich PhysicalExecution Inputs/actual Walk/after guard receipt, not raw done=>rich trace. The existing code Fields property is guard-only and cannot prove key-dependent arity by itself. No theorem Heap-before + generic Post => Heap-after is valid: new keys need their actual creation checks.

5. Prefix narrowing must compose actual MergedFreshOrdinaryExposure (including stored unfolding) with raw makeNode/filtering. makeNode itself leaves edgeRecords unchanged, but cold exposure can create copied edges, so caller Post.keeps alone is insufficient. Entry, own preparation/finalization and recordTypes callback mutate the ENUM cache; they keep the same native Caller heap. Carry the native Heap fact directly across their actual equations. Do not obtain Safe/Canonical/arity from a generic Frame.

6. Head/sibling composition must preserve initial Heap through EVERY actual native reached endpoint that can feed a later sibling. Raw [] rejection and admitted non-complete advance paths can retain native allocations. A successful-only complete-head proof is insufficient for later sibling origin transport. For a completed head, the callback strong IH must return Heap at its actual completed Hook caller and every emitted output's own caller. Keep SAME original captured cache for each sibling, but thread actual post-hook Caller/full Memos. Do not infer a full-Memos identity from queries. Absent stopped endpoints stay absent.

7. Strengthen the existing CompleteWithHistory contract by APPENDING an observer conditional on initial ArityOrigins.Heap, after its entire old bound/outcome/stable execution/OutcomeResources/unannotated-history packet. The observer returns ResourceHistoryWithArity at that SAME bound+extra/output plus Heap at actual available result endpoints and own outputs. Old admission and bound quantifier order stay unchanged. Structurally invariant observations can often use the existing sufficient bound; if a richer helper chooses another bound, choose a common sum/max BEFORE all extras/outputs and align actual old run equations. Do not assume every work fuel adequate for old Complete exceeds an independently chosen richer bound.

Exact proposed extra observer (schematic type aliases only; not an implemented theorem):
  initialArityHeap ->
    (match outcome with
     | .complete _ reached _ => ArityHeap reached.checked.native.machine.heap
     | .stopped _ _ endpoint => forall reached saved,
         endpoint=some(reached,saved) -> ArityHeap reached.checked.native.machine.heap) /\\
    forall extra output, output in hookOutputs outcome ->
      ArityHeap output.caller.checked.native.machine.heap /\\
      ResourceHistoryWithArity SAME original runtime parameters
        (bound+extra) SAME depth/inventory/caller/fullMemos/metadata/cache/seed/ceiling
        SAME actual Restart.decision SAME output

8. Derive each numeric ordinary annotation inside the ACTUAL head/sibling proof from Heap at that head's own native input, its real source selected edge/residency and current coherent Context. This preserves the entire existing ordinary receipt. The existing history/render theorems then supply acceptance without a new semantic admission. No additional history datatype is needed. Actual initial checked origin resource is the only new structural observer antecedent until the source-connected constructor producer derives it.

Small useful simplification: within one sibling scan all alternatives still use the SAME captured cache/parent stored edge list. Their already-checked original edges retain arity under old-record growth even if unrelated new records are created. This can reduce local annotation transport work. It does not replace full Heap preservation for newly produced pending handles used by smaller-depth callbacks.

First unavoidable gaps after the current constructors: actual native query step/optional-binder/cold-exposure preservation, full reached-Caller head rejection/advance cases, and stronger callback/sibling IH carrying the invariant at exact actual endpoints. These are operational source obligations; a numeric alias or separately assumed future arity cannot close them. No global history-origin theorem, coverage or physical Haskell correspondence is claimed by this proposal.
'''
save('transport-plan.txt',plan.encode())
report=f'''[{now}] Initial draft ready / OPEN.

Root's later scoped direction supersedes the earlier Parent-only history idea. No parallel history schema or converter was written. Concrete TEMP module SourcePruningEnumerationAllocatedOriginHeap110lines/{sha(own)} is saved immutable as drafts/v1. It proves real MkEdge.Receipt/RejectReceipt preservation of ENTIRE ArityOrigins.Heap from initial Heap through literal actual construction. The new public claims add no final Heap, fits/arity, desired Satisfies or future success premise. Actual post-construction coherence comes from the receipt. Existing APIs/runtime and all previous evidence are untouched.

The draft is UNCOMPILED by this worker and awaits Root serial strict checking. The source-only proof uses actual constructor inversion and requested-key record evidence. Every original input/result/heap endpoint stays the same. In Parent live construction, the missing local-reduction middle Heap remains an honest dependency, not an input disguised as established original preservation. Source snapshots/cuts and the separate transport-plan.txt identify actual missing native query/exposure/sibling/callback workers and exact common-bound order. No broad desired-gate history resource is introduced.

All used sources have exact whole identities; partial inspections are labeled. Shared ArityOrigins v5 was read by full v2 plus exact proof-elaboration-only diff. No Lean/compiler/build/Git/network/board or repository edits were performed. Prior frozen areas and the separate prior origin-contract-review are unchanged. Keep this new draft/review OPEN pending Root's actual strict source/report/raw and any necessary revision. This is not a new published or full history-origin claim.
'''
save('report.txt',report.encode());save('initial-report.txt',report.encode());put('source-index.json',{'schema':'whole sources and explicit literal cuts','cut_convention':'one-based inclusive; splitlines(keepends=True); original LF retained','sources':sources})
checks=0
for r in sources:
 d=Path(r['source']).read_bytes();assert d==Path(r['snapshot']).read_bytes() and len(d)==r['bytes'] and sha(d)==r['sha256'];checks+=1
 for c in r['cuts']:
  b=b''.join(d.splitlines(keepends=True)[c['first_line']-1:c['last_line']]);assert b==Path(c['snapshot']).read_bytes() and len(b)==c['bytes'] and sha(b)==c['sha256'];checks+=1
put('verification.json',{'status':'PASS input identities','checked_at':now,'source_records':len(sources),'literal_cuts':sum(len(x['cuts']) for x in sources),'byte_checks':checks,'draft_lean_check':'not run; uncompiled proposal','scope':'actual constructor heap preservation + exact missing history transport plan','status_area':'OPEN'})
put('OPEN.json',{'status':'OPEN','reviewed_at':now,'draft_sha256':sha(own),'reason':'Initial proof draft pending Root actual strict check; full history transport remains future work.'})
print(json.dumps({'status':'INITIAL DRAFT / OPEN','source_records':len(sources),'cuts':sum(len(x['cuts']) for x in sources),'byte_checks':checks,'draft_sha256':sha(own),'report_sha256':sha((O/'report.txt').read_bytes())},indent=2))
