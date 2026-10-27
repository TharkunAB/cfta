from pathlib import Path
from datetime import datetime
from zoneinfo import ZoneInfo
import hashlib,json
A=Path('/tmp/mcfta-history-checked-origins-20261027');O=A/'origin-contract-review';R=Path('/home/tritlo/Code/mcfta')
def sha(d):return hashlib.sha256(d).hexdigest()
def save(rel,d):
 p=O/rel;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(d);return {'snapshot':str(p),'bytes':len(d),'sha256':sha(d)}
def put(rel,x):return save(rel,(json.dumps(x,indent=2)+'\n').encode())
assert not (O/'FROZEN').exists()
records=[]
def cap(p,scope,spans):
 p=Path(p);d=p.read_bytes();rec={'source':str(p),**save('whole-inputs/'+p.name,d),'scope':'whole source identity; inspected extent stated separately','reviewed_scope':scope,'cuts':[]};records.append(rec)
 for first,last,why in spans:
  c=b''.join(d.splitlines(keepends=True)[first-1:last]);assert c
  rec['cuts'].append({'first_line':first,'last_line':last,**save(f'literal-cuts/{p.stem}-{first}-{last}.txt',c),'scope':'literal cut','purpose':why})
 return d
p=A/'arity-origin-review/SourcePruningEnumerationAllocatedOriginArity.lean';draft=cap(p,'WHOLE192line initial uncompiled proposal read',[(1,21,'declared scope and imports'),(23,73,'entire checked MkEdge receipt arity proof'),(75,92,'entire raw-rejected receipt arity proof'),(103,121,'entire Parent receipt composition'),(140,190,'entire actual selected-head origin transport')]);assert sha(draft)=='1aeb522dc703d518c6a6ea44ed2fadba72cdbaa0840b29c0c620de5fdcc96a81'
revision=(A/'arity-origin-review/revisions/v1.lean').read_bytes();assert revision==draft;save('draft-revisions/v1.lean',revision)
cap(R/'lean/MicroCFTA/SourceCurrentAllocatedMkEdge.lean','WHOLE217line actual runtime/receipts/producers read',[(35,80,'actual build/reject and exact receipt fields'),(109,150,'existing finite producer derives both live and sentinel receipts'),(163,177,'existing raw reject producer')])
cap(R/'lean/MicroCFTA/SourceCurrentAllocatedParentEdge.lean','WHOLE210line parent runtime/receipts/producers read',[(34,46,'actual rejected/live source ordering'),(77,100,'entire parent receipt and both construction branches'),(149,207,'existing actual finite producer supplies construction at same returned result/state')])
cap(R/'lean/MicroCFTA/SourcePruningEnumerationOwnArity.lean','WHOLE prior accepted-projection arity proof read',[(11,37,'prior lower-level explicit checked inputs/result'),(49,99,'accepted fit/root-bound derivation and fresh arity')])
cap(R/'lean/MicroCFTA/SourcePruningEnumerationHeadCheckedArity.lean','WHOLE95line prior actual-head transport read',[(28,95,'prior source-connected transport and complete residency/identity equality')])
cap(R/'lean/MicroCFTA/SourcePruningEnumerationConstraint.lean','WHOLE90line actual projection and normalized projection proof read',[(9,38,'runtime projection and exact normalized-path theorem'),(47,58,'normal-class readback and valid tries')])
cap(R/'lean/MicroCFTA/SourceEqualityMkEdgeArity.lean','ONLY lines17-46 read for exact natural root bounds',[(17,46,'signed-path bound and exact accepted fits characterization')])
cap(R/'lean/MicroCFTA/SourceEqualityMkEdgeAllocation.lean','ONLY lines18-45 read for actual accepted/fits/contradiction control',[(18,45,'actual source fits/accepted definition')])
cap(R/'lean/MicroCFTA/SourceCurrentConjunctionEquality.lean','ONLY lines1-45 read; FieldAvailable/Fields normalized current annotation route',[(21,28,'actual normalized current guard fields')])
cap(R/'lean/MicroCFTA/InternedEdgeResidency.lean','ONLY lines1-65 and150-180 read for actual growth/residency/identity transport',[(20,44,'complete EdgeResident and growth/selected resident producer'),(157,166,'same identity implies complete record and ordered payload equality')])
now=datetime.now(ZoneInfo('Europe/Stockholm')).isoformat()
review=f'''[{now}] CLEAR / OPEN: initial Parent/MkEdge origin arity proposal.

WHOLE SourcePruningEnumerationAllocatedOriginArity192lines/{sha(draft)} read against exact existing constructor and Parent receipts/producers. Revisionv1 is byte-identical. This is a source-only semantic review. No Lean/compiler/build/Git/network/board or repository edit occurred. No actual strict receipt exists in this review yet. Earlier frozen evidence areas are untouched.

Four local statements are sound as written. Checked MkEdge Receipt.projected_arity uses actual receipt.ready.good.fields at receipt.resident to obtain normalized cached equality classes. The stored guard/children equalities split the real source accepted Bool. Accepted=true DERIVES fits from accepted's definition, rather than assuming fits or desired arity. fits_exact supplies natural root-child bounds. project_complete gives valid actual tries and exact path readback; deterministic projection identifies the same returned tries/residual. Those bounds prove fresh arity for EVERY start on the ACTUAL returned children. Accepted=false rewrites the actual returned guard to Top, so any successful own projection is empty and fresh arity is immediate at every child length. It does not assert that the rejected sentinel accepts a source term.

RejectReceipt.projected_arity consumes its exact Top guard and derives the same empty projection without any child availability premise. Parent Receipt.projected_arity uses the EXISTING construction field: raw rejection carries RejectReceipt, while the live branch carries the exact MkEdge Receipt at the actual local-reduction middle and SAME result/after. Existing Parent.finite constructs these fields in both branches. No input arity/Valid/fits/desired Satisfies premise is added. The old receipt also contains independent semantic language fields, but this numeric proof does not use them or introduce a new desired semantic law.

CompletedHeadReceipt.freshArity_of_parent_construction correctly consumes genuine original Parent receipt plus originCaller heap equation, actual full Post from originCaller to current HEAD INPUT caller/full Memos, and SAME edge identity. origin.resident survives Post.effects.keeps.growth at the actual current native heap. The current head's actual stored/decoded/selected source and Packet.PendingRealized identify its parent; current Context provides linked/coherent records. This derives selected edge residency. edge_identity_unique then DERIVES complete canonical edge/ordered child payload equality; it does not assume arbitrary identities identify records in a malformed heap. Original projection arity is transported to exactly before.core.counter. Native source/current/reached callers, source/current inventories, full Memos and captured cache remain distinct actual parameters. There is no arbitrary heap rebase or full-Memos equality inferred from queries.

No actionable mathematical defect found. The module introduces local provenance consumers only; old source declarations/runtime/producers remain unchanged. It neither claims every Packet has Parent construction provenance nor derives a global ordinary-history arity decoration. The next real step is to retain actual constructor/intersection origin receipts and matching canonical identity across heap Posts to EACH selected recursive head. Intersection-created edges and any other origin cases need their own real source receipt; this Parent-only theorem does not cover them by implication. Keep global origin/history production, coverage and physical Haskell correctness open.

Recommended action: strict-check this unchanged proposal under the existing capped serial workflow. No extra arity or semantic input is needed. A later bound review should bind the exact installed strict snapshot/report/raw before any checked/final claim. Whole-source identities and focused literal cuts are explicit in source-index.json. Partial original-source reads are labeled partial. Keep this review OPEN pending Root's actual strict check and any requested integration review.
'''
save('report.txt',review.encode());save('initial-review.txt',review.encode());put('source-index.json',{'schema':'whole sources and explicit literal cuts','cut_convention':'one-based inclusive; splitlines(keepends=True); original LF retained','sources':records})
checks=0
for rec in records:
 d=Path(rec['source']).read_bytes();assert d==Path(rec['snapshot']).read_bytes() and len(d)==rec['bytes'] and sha(d)==rec['sha256'];checks+=1
 for c in rec['cuts']:
  b=b''.join(d.splitlines(keepends=True)[c['first_line']-1:c['last_line']]);assert b==Path(c['snapshot']).read_bytes() and len(b)==c['bytes'] and sha(b)==c['sha256'];checks+=1
put('verification.json',{'status':'PASS','checked_at':now,'source_records':len(records),'literal_cuts':sum(len(r['cuts']) for r in records),'byte_checks':checks,'draft_revision_v1_exact':True,'strict_execution':'not performed by reviewer; no receipt yet','review_status':'CLEAR / OPEN'})
put('OPEN.json',{'status':'OPEN','reviewed_at':now,'reason':'Initial source review clear; Root strict check not yet bound.','draft_sha256':sha(draft)})
print(json.dumps({'status':'CLEAR / OPEN','draft_sha256':sha(draft),'sources':len(records),'cuts':sum(len(r['cuts']) for r in records),'byte_checks':checks,'report_sha256':sha((O/'report.txt').read_bytes()),'source_index_sha256':sha((O/'source-index.json').read_bytes())},indent=2))
