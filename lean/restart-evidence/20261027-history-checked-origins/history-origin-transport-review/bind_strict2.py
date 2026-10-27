from pathlib import Path
from datetime import datetime
from zoneinfo import ZoneInfo
import hashlib,json,shutil
A=Path('/tmp/mcfta-history-checked-origins-20261027');O=A/'history-origin-transport-review'
def sha(d):return hashlib.sha256(d).hexdigest()
def save(rel,d):
 p=O/rel;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(d);return {'snapshot':str(p),'bytes':len(d),'sha256':sha(d)}
def put(rel,v):return save(rel,(json.dumps(v,indent=2)+'\n').encode())
assert not (O/'FROZEN').exists();h=O/'review-revisions/before-strict2';h.mkdir(parents=True,exist_ok=True)
for n in ['report.txt','source-index.json','verification.json','OPEN.json']:
 assert not (h/n).exists();shutil.copyfile(O/n,h/n)
records=json.loads((O/'source-index.json').read_text())['sources'];phase='strict-allocated-origin-heap-2';name='SourcePruningEnumerationAllocatedOriginHeap';data={}
for rel in [f'MicroCFTA/{name}.lean','report.json','raw.log']:
 p=A/phase/rel;d=p.read_bytes();data[rel]=d;records.append({'source':str(p),**save('actual-strict/'+phase+'/'+rel,d),'scope':'whole actual strict source/report/output identity','reviewed_scope':'whole report/raw read; actual source byte-equal to fully reviewed final115line v2','cuts':[]})
r=json.loads(data['report.json']);source=data[f'MicroCFTA/{name}.lean'];raw=data['raw.log'];assert source==(O/f'drafts/v2/{name}.lean').read_bytes() and sha(source)==r['source_sha256']=='d75f884761a0169dc2f38b5080b17437e96eed89af4b5f37379c4c4cc4833aac';assert r['exit_code']==0 and len(raw)==r['bytes']==0 and sha(raw)==r['sha256'];assert r['cgroup_limits']=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
now=datetime.now(ZoneInfo('Europe/Stockholm')).isoformat()
report=f'''[{now}] CLEAR / OPEN — actual allocated constructor preservation of the entire edge-arity table.

Final TEMP SourcePruningEnumerationAllocatedOriginHeap115lines/7122B/SHAd75f884761a0169dc2f38b5080b17437e96eed89af4b5f37379c4c4cc4833aac matches actual strict-allocated-origin-heap-2 source byte exactly. Strict2 PASS0/raw0, all linters and warnings fatal, actual memory.max/high4GiB,swap0. V1 and its actual strict1 failure1231B are retained. The sole failed goal was private makeEdge_record's unreduced requested-key let; v2 only folds the actual key/candidate explicitly before simp. All FOUR declaration headers are byte-identical; both public contracts stay unchanged. No source/build/Lean/compiler/Git/network/board action was run by this worker.

Receipt.preserves_arity_heap consumes the ACTUAL original MkEdge.Receipt and the ENTIRE initial key-dependent ArityOrigins.Heap, then derives Heap at EXACT actual after.native.machine.heap. RejectReceipt.preserves_arity_heap does the same for the real raw rejection constructor, without child availability. There is no final Heap, desired arity/fits, Satisfies or future successful action premise. Existing old runtime/producer contracts are untouched.

The proof inverts receipt.actual once across its real checked result. A checked error cannot equal the supplied actual successful constructor receipt. Both real Bool branches identify the selected raw makeEdge/result/heap. keepFirst_present supplies the exact requested key's actual returned record even on canonical hits. Returned coherence derives guard and child-count equality between that key and actual result payload. The already derived receipt.projected_arity provides Fits of this exact guard/count. Shared edge_heap checks the actual requested key and retains EVERY old record; this proves the WHOLE table, not only the returned edge's arity. No before Ready/extra physical read or arbitrary generic Post-to-Heap law is needed.

The separate source-pinned transport-plan.txt identifies the remaining real obligations. Parent live construction starts its final checked step at the actual LocalReduction MIDDLE. The new lemma preserves Heap from that middle. Original-before Parent Heap alone does not cover new records inserted by reduction/child queries. Native checked step/query/optional-binder/cold-exposure stopping prefixes must preserve the key-dependent invariant. A generic native Post retains old records but does not check new keys. Guard-only annotations/Context must not be substituted for this property.

For whole recursion, preserve Heap on EVERY actual native head endpoint that can advance to another sibling, including raw[] rejection, then through actual callback recursion at returned Caller/FULL Memos and own output heaps. The captured cache remains fixed per sibling; post-hook native effects still thread. Entry and recordTypes enum frames keep native Caller unchanged. An original-input conditional observer can append SAME-bound ResourceHistoryWithArity to the ENTIRE existing finite producer packet after actual creation preservation is proved. Keep one common bound before all extras/outputs; never assume old sufficient fuels exceed an independently chosen richer helper bound. No Parent-only parallel history schema or renamed numeric gate was added.

The bounded implementation/review is COMPLETE CLEAR. Exact used sources, literal cuts, initial drafts, failure/correction and public header comparison are retained. Global production of all arity-certified histories, coverage and physical Haskell correctness remain OPEN. This does not assert a new installed/build/public/published checkpoint; Root owns that later integration. Keep this area/review OPEN for further requested integration evidence. Previous frozen areas and the separate prior origin-contract-review remain untouched.
'''
save('report.txt',report.encode());save('strict2-final-review.txt',report.encode());put('source-index.json',{'schema':'whole sources and explicit literal cuts','cut_convention':'one-based inclusive; splitlines(keepends=True); original LF retained','sources':records});checks=0
for rec in records:
 d=Path(rec['source']).read_bytes();assert d==Path(rec['snapshot']).read_bytes() and len(d)==rec['bytes'] and sha(d)==rec['sha256'];checks+=1
 for c in rec['cuts']:
  part=b''.join(d.splitlines(keepends=True)[c['first_line']-1:c['last_line']]);assert part==Path(c['snapshot']).read_bytes() and len(part)==c['bytes'] and sha(part)==c['sha256'];checks+=1
put('verification.json',{'status':'PASS','checked_at':now,'source_records':len(records),'literal_cuts':sum(len(x['cuts']) for x in records),'byte_checks':checks,'final_strict2_pass':True,'v1_failed_source_report_raw_preserved':True,'all_four_headers_byte_exact':True,'bounded_review':'COMPLETE CLEAR','whole_area_status':'OPEN; later integration/history transport not claimed'})
put('OPEN.json',{'status':'OPEN','reviewed_at':now,'bounded_constructor_proof_review':'COMPLETE CLEAR','final_source_sha256':sha(source),'final_strict':'strict-allocated-origin-heap-2 PASS0/raw0','reason':'Future actual query/history integration, installed/build/public claims remain Root work.'})
print(json.dumps({'status':'CLEAR / OPEN','source_records':len(records),'literal_cuts':sum(len(x['cuts']) for x in records),'byte_checks':checks,'report_sha256':sha((O/'report.txt').read_bytes()),'source_index_sha256':sha((O/'source-index.json').read_bytes())},indent=2))
