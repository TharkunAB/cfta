from pathlib import Path
from datetime import datetime
from zoneinfo import ZoneInfo
import hashlib,json
A=Path('/tmp/mcfta-history-boundary-exclusion-20261027');O=A/'gates-review';R=Path('/home/tritlo/Code/mcfta')
def sha(d):return hashlib.sha256(d).hexdigest()
def save(rel,d):
 p=O/rel;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(d);return {'snapshot':str(p),'bytes':len(d),'sha256':sha(d)}
def put(rel,x):return save(rel,(json.dumps(x,indent=2,ensure_ascii=False)+'\n').encode())
records=[]
def capture(source,rel,spans,reviewed):
 source=Path(source);d=source.read_bytes();r={'source':str(source),**save(rel,d),'scope':'whole source/evidence identity','reviewed_scope':reviewed,'cuts':[]};records.append(r)
 for first,last,reason in spans:
  assert 1<=first<=last<=len(d.splitlines(keepends=True)),(source,last)
  c=b''.join(d.splitlines(keepends=True)[first-1:last]);r['cuts'].append({'first_line':first,'last_line':last,**save(f'cuts/{source.stem}-{first}-{last}.txt',c),'scope':'literal cut','purpose':reason})
 return d
name='SourcePruningEnumerationHeadCheckedArity';expected='c4c0cffd396623a819cf67660f9be78f8f4e4cd19701c65c0e82ec1ea2dcfa4a'
source=capture(A/f'checked-arity-draft/{name}.lean',f'whole/{name}.lean',[(1,26,'complete module context'),(28,59,'entire current head plus genuine checked-build provenance admission and forall projection conclusion'),(60,93,'actual checked receipt, resident-edge transport, full record equality and current fresh arity')],'WHOLE 95-line source read')
assert sha(source)==expected and len(source.splitlines())==95
inputs=[
 ('SourcePruningEnumerationCheckedArity',[(9,47,'entire original checked constructor receipt and own arity'),(48,109,'both accepted and rejected sentinel proof paths')],'whole module read'),
 ('InternedEdgeResidency',[(20,44,'complete edge record residency, growth and selected parent edge extraction'),(157,167,'coherent same-identity implies full edge record equality')],'lines1-60 and140-180 read; focused cuts cover used APIs'),
 ('SourceEqualityRequiredCache',[(18,39,'Ready and exact Keeps growth/history'),(53,60,'actual constructed edge residency')],'lines1-60 read; whole identity retained'),
 ('SourcePruningEnumerationHeadAdmission',[(40,102,'entire existing head admission and completed receipt fields')],'lines35-105 read; exact original receipt scope retained'),
 ('SourceEqualityMkEdgeAllocation',[(23,45,'source accepted check and short circuit'),(68,74,'source accepted edge vs rejected sentinel runtime')],'lines1-75 read; old constructor API is used through existing checked theorem'),
 ('SourceCurrentAllocatedPartialInvariant',[(24,46,'actual caller Context and full Post/effects')],'lines20-55 read; full identity retained')
]
for stem,spans,scope in inputs:capture(R/f'lean/MicroCFTA/{stem}.lean',f'inputs/{stem}.lean',spans,scope)
checked=capture(A/f'strict-head-checked-arity-1/MicroCFTA/{name}.lean',f'strict/{name}.lean',[],'whole strict checked source byte-equal to reviewed draft')
report=capture(A/'strict-head-checked-arity-1/report.json','strict/report.json',[],'whole actual strict report read')
raw=capture(A/'strict-head-checked-arity-1/raw.log','strict/raw.log',[],'whole empty actual raw log read')
r=json.loads(report);assert checked==source and r['source_sha256']==expected and r['exit_code']==0 and r['bytes']==len(raw)==0 and r['sha256']==sha(raw)
assert r['cgroup_limits']=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
assert source.count(b'SourcePruningEnumerationCheckedArity.checked_projected_arity')==1
start=source.index(b'theorem CompletedHeadReceipt.freshArity_of_checked_build\n');end=source.index(b' := by\n',start)
save('contracts/new-full-header.txt',source[start:end])
old=(R/'lean/MicroCFTA/SourcePruningEnumerationCheckedArity.lean').read_bytes();start=old.index(b'theorem checked_projected_arity ');end=old.index(b' := by\n',start);save('contracts/original-checked-producer-header.txt',old[start:end])
now=datetime.now(ZoneInfo('Europe/Stockholm')).isoformat()
text=f'''[{now}] CLEAR / OPEN: actual checked constructor provenance supplies fresh arity for the same captured head edge.

Reviewed WHOLE new source: SourcePruningEnumerationHeadCheckedArity, 95 lines, SHA256 {expected}. The actual strict-head-checked-arity-1 source is byte-identical. The check exits0/raw0 with warningAsError/all linters, actual memory.max/high 4,294,967,296 bytes and swap.max0. No build/Lean/Git/network/board action was run for this review. Earlier frozen areas were not changed.

The theorem is a new local consumer of the actual CompletedHeadReceipt and explicit past checked-build provenance. Its inputs retain the real stored equality payload/Cached/physical-read/Ready/operationsValid/sourceHeap Ready and accepted-children availability. The actual build returns builtEdge/builtOperations/builtHeap. A builtCaller heap equation and actual Post to the CURRENT head input caller retain that build. The only matching-edge premise is identity equality, not current full payload equality or the desired current arity.

The original checked_projected_arity producer is called ONCE. It covers both accepted construction and rejected sentinel construction and supplies its exact build receipt, complete edge residency, deterministic own projection and forall-start fresh arity. The actual supplied build equation identifies its returned edge and heap without rerunning the constructor. Post.effects.keeps transports complete EdgeResident to the current caller heap.

The actual current stored parent comes from head.admission.source and packet.valid.realized. The lookup equations identify that parent with the ordinary node containing the selected edge. Current Context provides the linked and coherent heap. These facts derive selected EdgeResident; edge_identity_unique then derives equality of COMPLETE canonical records and ordered child payloads from matching identity. The final arbitrary successful projection equals the checked producer's projection. Its tries and own-arity bound therefore apply at before.core.counter, using the producer's forall-start result.

No circular arity or desired Satisfies premise was found. No universal Ranges premise, current final Canonical, future callback completion or future successful runtime action is added. Native caller, captured cache, metadata and full Memos stay those of the original receipt; no query equality substitutes for full Memos. This theorem does not claim that Packet alone contains checked-constructor provenance. A later whole-history consumer still needs genuine build/intersection provenance for each current selected edge. The theorem only discharges fresh arity where its explicit original build/Post/identity receipts are supplied. It does not establish whole-language acceptance, coverage, or physical Haskell execution correctness.

The existing checked constructor theorem and all old APIs remain unchanged; this new local consumer is not a replacement producer with a copied old output contract. Exact full new and original checked-producer headers are retained under contracts/. source-index.json records the focused original source APIs, exact whole identities and literal cuts. This review stays OPEN for actual output-discharge child-retention/integration and final source/build/public/Audit/claim receipts.
'''
save('report.txt',text.encode())
put('source-index.json',{'schema':'whole sources and explicit literal cuts','cut_convention':'one-based inclusive lines; splitlines(keepends=True); original LF retained','sources':records})
put('arity-check.json',{'status':'CLEAR','reviewed_at':now,'source_sha256':expected,'line_count':95,'old_checked_producer_calls':1,'actual_build_equation':True,'past_heap_equation_and_retained_post':True,'selected_residency_derived':True,'full_edge_record_equality_derived':True,'forall_projection_arity_at_current_counter_derived':True,'packet_alone_not_claimed':True,'strict_exit_code':0,'strict_raw_bytes':0,'actual_memory_max':4294967296,'swap_max':0})
put('OPEN.json',{'status':'OPEN','reviewed_at':now,'current_review':'CLEAR checked-arity source/receipt','reason':'Await actual retention proof and consumer integration, then final installed/build/public/Audit/document claims.','publication_outcome':'not asserted'})
print(json.dumps({'status':'CLEAR / OPEN','report_sha256':sha((O/'report.txt').read_bytes()),'source_index_sha256':sha((O/'source-index.json').read_bytes()),'whole_records':len(records),'cuts':sum(len(x['cuts']) for x in records)},indent=2))
