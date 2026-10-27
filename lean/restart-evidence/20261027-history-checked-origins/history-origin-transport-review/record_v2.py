from pathlib import Path
from datetime import datetime
from zoneinfo import ZoneInfo
import hashlib,json,shutil,re
A=Path('/tmp/mcfta-history-checked-origins-20261027');O=A/'history-origin-transport-review'
def sha(d):return hashlib.sha256(d).hexdigest()
def save(rel,d):
 p=O/rel;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(d);return {'snapshot':str(p),'bytes':len(d),'sha256':sha(d)}
def put(rel,x):return save(rel,(json.dumps(x,indent=2)+'\n').encode())
assert not (O/'FROZEN').exists();history=O/'review-revisions/before-v2';history.mkdir(parents=True,exist_ok=True)
for n in ['source-index.json','report.txt','verification.json','OPEN.json']:
 assert not (history/n).exists();shutil.copyfile(O/n,history/n)
records=json.loads((O/'source-index.json').read_text())['sources']
def cap(p,rel,scope,spans=()):
 p=Path(p);d=p.read_bytes();rec={'source':str(p),**save(rel,d),'scope':'whole exact source/evidence identity','reviewed_scope':scope,'cuts':[]};records.append(rec)
 for first,last,why in spans:
  c=b''.join(d.splitlines(keepends=True)[first-1:last]);rec['cuts'].append({'first_line':first,'last_line':last,**save(f'v2-literal-cuts/{p.stem}-{first}-{last}.txt',c),'scope':'literal cut','purpose':why})
 return d
name='SourcePruningEnumerationAllocatedOriginHeap';v1=(O/f'drafts/v1/{name}.lean').read_bytes();v2=cap(O/f'drafts/v2/{name}.lean',f'proof-revisions/v2-{name}.lean','whole115line v2 reviewed; only raw record helper elaboration changed',[(24,40,'explicit actual requested key/candidate reduction'),(58,91,'unchanged public checked constructor contract and proof'),(93,113,'unchanged public rejection contract and proof')]);assert sha(v2)=='d75f884761a0169dc2f38b5080b17437e96eed89af4b5f37379c4c4cc4833aac'
def headers(d):
 out={}
 for m in re.finditer(rb'^(?:private )?theorem ([A-Za-z0-9_.]+)\n',d,re.M):out[m.group(1).decode()]=d[m.start():d.index(b' := by\n',m.start())]
 return out
h1,h2=headers(v1),headers(v2);assert h1==h2 and len(h1)==4
for name1,header in h1.items():save('contracts/'+name1+'.txt',header)
put('revision-contracts.json',{'status':'PASS','all_four_declaration_headers_byte_exact':True,'public_theorems':['Receipt.preserves_arity_heap','RejectReceipt.preserves_arity_heap'],'v1_sha256':sha(v1),'v2_sha256':sha(v2),'only_change':'Explicit folded key/candidate change followed by present rewrite in private makeEdge_record proof.','no_runtime_changes':True})
phase='strict-allocated-origin-heap-1';strictSource=cap(A/phase/f'MicroCFTA/{name}.lean',f'actual-strict/{phase}/{name}.lean','whole actual failed source equals immutable reviewed v1');report=cap(A/phase/'report.json',f'actual-strict/{phase}/report.json','whole failed strict report read');raw=cap(A/phase/'raw.log',f'actual-strict/{phase}/raw.log','whole sole key-let simplification failure read')
r=json.loads(report);assert strictSource==v1 and r['source_sha256']==sha(v1) and r['exit_code']==1 and len(raw)==r['bytes']==1231 and sha(raw)==r['sha256'];assert r['cgroup_limits']=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
# Add the exact complete construction dependency theorem cut; original narrower literal cut remains intact.
p=A/'origin-propagation-review/drafts/v5/SourcePruningEnumerationArityOrigins.lean';d=p.read_bytes();c=b''.join(d.splitlines(keepends=True)[240:247]);rec=next(x for x in records if x['source']==str(p));rec['cuts'].append({'first_line':241,'last_line':247,**save('v2-literal-cuts/ArityOrigins-constructed_heap-241-247.txt',c),'scope':'literal cut','purpose':'ENTIRE actual original checked-construction Heap derivation'})
now=datetime.now(ZoneInfo('Europe/Stockholm')).isoformat();review=f'''[{now}] Draft v2 ready / OPEN.

The bounded history-origin task now supplies a concrete 115-line constructor preservation proof rather than a Parent-only parallel history API. Immutable v2 SHAd75f884761a0169dc2f38b5080b17437e96eed89af4b5f37379c4c4cc4833aac is in drafts/v2/SourcePruningEnumerationAllocatedOriginHeap.lean. All FOUR declaration headers, including both public Receipt.preserves_arity_heap and RejectReceipt.preserves_arity_heap, remain byte-identical to v1. Each consumes the ACTUAL existing receipt plus entire initial ArityOrigins.Heap and concludes the ENTIRE exact returned Heap. No final Heap, desired fits/arity or Satisfies premise is added.

Actual Root strict1 checked v1 at4GiB/swap0. It failed ONLY private makeEdge_record's simpa (1231B), because the requested-key let had not reduced in the target while present simplified to True. All remaining proof paths elaborated. Immutable v2 changes ONLY that helper body: explicit change to keepFirst at the same folded requested key/candidate, then simp[present,Option.getD_some]. It has NOT yet received a terminal strict check in this review. Exact v1 source/report/raw and correction remain preserved; no failed source is counted as a pass.

The mathematical proof is concrete. Actual receipt.actual chooses the literal checked makeEdge branch once. The returned receipt's coherent record identifies the requested guard and child count with the ACTUAL returned payload. Its existing projected_arity supplies the new key's Fits. Shared edge_heap retains every old record and checks the actual new key, including canonical hits. Raw rejection needs no child availability. Parent live construction can apply this at its real local-reduction MIDDLE; preservation from original Parent-before still needs real reduction/query invariant preservation and is not asserted.

transport-plan.txt gives the exact next route: derive the initial KEY-DEPENDENT Heap from checked syntax/actual raw build; preserve it through actual native checked step/query/optional-binder/cold exposure prefixes; retain it on EVERY actual head advance including [] rejection; propagate it through actual callback recursion at its returned Caller/full Memos and each own output heap. Same captured cache is fixed per sibling; post-hook native effects still thread. Entry/recordTypes enum frames keep native Caller unchanged. Existing guard-only Heap/Context/Post do not establish arity of newly inserted keys. No generic Post->Heap theorem or new desired-gate alias is proposed.

The existing CompleteWithHistory packet can remain ENTIRE and choose its common bound BEFORE extras/outputs, then append an initial-source-Heap conditional observer yielding SAME-bound ResourceHistoryWithArity and actual endpoint invariants. Actual creation preservation must discharge this observer; it is not a future-result premise. If a new helper needs a larger bound, align at an original-input common sum/max rather than assume all old sufficient fuels exceed it. Global all-path origin production, coverage and physical Haskell correspondence remain OPEN.

No repo/Lean/compiler/build/Git/network/board action was performed by this worker. Prior frozen areas and previous separate review remain unchanged. New area stays OPEN pending actual strict2 and later installation/build/public integration. Full source identities and meaningful literal cuts are explicit; the whole-history converter was deliberately not duplicated.
'''
save('report.txt',review.encode());save('v2-review.txt',review.encode());put('source-index.json',{'schema':'whole sources and explicit literal cuts','cut_convention':'one-based inclusive; splitlines(keepends=True); original LF retained','sources':records});checks=0
for rec in records:
 d=Path(rec['source']).read_bytes();assert len(d)==rec['bytes'] and sha(d)==rec['sha256'] and d==Path(rec['snapshot']).read_bytes();checks+=1
 for c in rec['cuts']:
  dcut=b''.join(d.splitlines(keepends=True)[c['first_line']-1:c['last_line']]);assert dcut==Path(c['snapshot']).read_bytes() and len(dcut)==c['bytes'] and sha(dcut)==c['sha256'];checks+=1
put('verification.json',{'status':'PASS source/contract bytes','checked_at':now,'source_records':len(records),'literal_cuts':sum(len(x['cuts']) for x in records),'byte_checks':checks,'v1_strict_failure_preserved':True,'v2_status':'submitted, no terminal strict receipt yet','all_public_headers_exact':True,'review_area':'OPEN'})
put('OPEN.json',{'status':'OPEN','reviewed_at':now,'draft_sha256':sha(v2),'reason':'V1 sole helper elaboration failure preserved; v2 pending Root serial strict check.'})
print(json.dumps({'status':'V2 READY / OPEN','sources':len(records),'cuts':sum(len(x['cuts']) for x in records),'byte_checks':checks,'report_sha256':sha((O/'report.txt').read_bytes()),'source_index_sha256':sha((O/'source-index.json').read_bytes())},indent=2))
