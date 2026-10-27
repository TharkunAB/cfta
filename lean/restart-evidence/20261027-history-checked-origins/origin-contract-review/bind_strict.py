from pathlib import Path
from datetime import datetime
from zoneinfo import ZoneInfo
import hashlib,json,shutil
A=Path('/tmp/mcfta-history-checked-origins-20261027');O=A/'origin-contract-review';name='SourcePruningEnumerationAllocatedOriginArity'
def sha(d):return hashlib.sha256(d).hexdigest()
def save(rel,d):
 p=O/rel;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(d);return {'snapshot':str(p),'bytes':len(d),'sha256':sha(d)}
def put(rel,v):return save(rel,(json.dumps(v,indent=2)+'\n').encode())
assert not (O/'FROZEN').exists()
h=O/'review-revisions/before-terminal-strict';h.mkdir(parents=True,exist_ok=True)
for n in ['report.txt','source-index.json','verification.json','OPEN.json']:
 assert not (h/n).exists();shutil.copyfile(O/n,h/n)
records=json.loads((O/'source-index.json').read_text())['sources'];results=[]
for attempt in [1,2]:
 phase=f'strict-allocated-origin-arity-{attempt}';pieces={}
 for rel in [f'MicroCFTA/{name}.lean','report.json','raw.log']:
  p=A/phase/rel;d=p.read_bytes();rec={'source':str(p),**save('actual-strict/'+phase+'/'+rel,d),'scope':'whole executed strict source/report/output identity','reviewed_scope':'whole report/raw read; whole source compared to exact reviewed revision','cuts':[]};records.append(rec);pieces[rel]=d
 r=json.loads(pieces['report.json']);source=pieces[f'MicroCFTA/{name}.lean'];raw=pieces['raw.log'];expected=(O/f'draft-revisions/v{attempt}.lean').read_bytes();assert source==expected and sha(source)==r['source_sha256'] and len(raw)==r['bytes'] and sha(raw)==r['sha256']
 assert r['cgroup_limits']=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
 if attempt==1:assert r['exit_code']==1 and len(raw)==629 and b'unused in theorem' in raw and b'[DecidableEq Symbol]' in raw and b'[DecidableEq (Value Symbol Constraint)]' in raw
 else:assert r['exit_code']==0 and raw==b''
 results.append({'attempt':attempt,'source_bytes':len(source),'source_lines':len(source.splitlines()),'source_sha256':sha(source),'exit_code':r['exit_code'],'raw_bytes':len(raw),'raw_sha256':sha(raw),'actual_memory_max':r['cgroup_limits']['memory.max'],'actual_memory_swap_max':r['cgroup_limits']['memory.swap.max']})
now=datetime.now(ZoneInfo('Europe/Stockholm')).isoformat()
report=f'''[{now}] CLEAR / OPEN — checked local allocated-origin arity consumers.

Read WHOLE original192line v1 and final191line v2 (full original plus exact two-unused-instance removal), against actual MkEdge/ParentEdge receipt definitions and producers. Final source22d8c52273f24566d05a9355c6f03df043f643c4c02007638085f92a64379357 matches actual strict-allocated-origin-arity-2 source byte exactly. Strict2 PASS exit0/raw0, all linters/warnings fatal, actual memory.max/high4GiB and swap0. Strict1 failed ONLY two unused Parent namespace section instances (629B diagnostic); exact failed source/report/raw and both revisions remain preserved. The review's initial capture detected the concurrent source update by an expected-v1 assertion; that data-capture correction is retained separately and is not called a Lean failure.

No mathematical blocker found. Actual MkEdge Receipt.ready.good.fields and exact guard/child receipts supply normalized equality projection. Source accepted=true DERIVES fits and natural root-path bounds; project_complete identifies valid returned tries. This gives fresh own arity for EVERY start at actual returned child length. Rejection rewrites actual guard to Top and derives empty projection without available-child or desired acceptance assumptions. Parent Receipt.construction supplies either the actual raw RejectReceipt or SAME result/after's checked constructor receipt following local reduction. Existing Parent.finite genuinely produces both; no new fits, arity, semantic truth or future-success premise is introduced.

Final head transport uses genuine original Parent receipt, originCaller heap equation, ACTUAL retained full Post to current head-input caller/full Memos and matching edge identity. The old resident edge grows into that same current heap. Head source stored/decoded/selected facts and Packet.PendingRealized derive current parent availability; current Context supplies linked/coherent records. Both complete EdgeResident receipts plus identity DERIVE full ordered edge-record equality. The actual projected tries therefore have own arity at exactly the captured before.core.counter. Source/current/reached callers, inventories, native heaps, full Memos, metadata and cache remain explicit distinct parameters. No generic heap rebase or full-Memos equality from query equality is used.

These are four local consumers. They do not produce checked construction/intersection origin history for every recursive selected edge or derive global ResourceHistoryWithArity from Packet. A Parent receipt contains existing independent semantic language fields, but this numeric proof uses no desired semantic law. Next actual work must retain source constructor/intersection origin receipts and matching canonical edge identities through native Posts to EACH selected head. Coverage and physical Haskell correctness remain open.

This bounded review is complete, with exact whole identities and explicitly labeled literal cuts. Root reports the draft is NOT yet installed, built or included in a new public checkpoint. These new theorems are NOT part of the preceding published claim. No repository/Git/build/Lean/network/board action was performed by this reviewer; prior frozen areas are untouched. Keep this new area and review OPEN for future installed/build/public integration. Do not infer a whole-area freeze from this source review.
'''
save('report.txt',report.encode());save('terminal-strict-review.txt',report.encode());put('strict-attempts.json',{'status':'PASS final strict binding; historical failure retained','attempts':results,'v1_to_v2_only_unused_section_instances':True,'installation':'not claimed','build_public':'not claimed'})
put('source-index.json',{'schema':'whole sources and explicit literal cuts','cut_convention':'one-based inclusive; splitlines(keepends=True); original LF retained','sources':records})
checks=0
for rec in records:
 d=Path(rec['source']).read_bytes();assert len(d)==rec['bytes'] and sha(d)==rec['sha256'] and d==Path(rec['snapshot']).read_bytes();checks+=1
 for c in rec['cuts']:
  dcut=b''.join(d.splitlines(keepends=True)[c['first_line']-1:c['last_line']]);assert dcut==Path(c['snapshot']).read_bytes() and len(dcut)==c['bytes'] and sha(dcut)==c['sha256'];checks+=1
put('verification.json',{'status':'PASS','checked_at':now,'source_records':len(records),'literal_cuts':sum(len(r['cuts']) for r in records),'byte_checks':checks,'final_strict_pass':True,'historical_strict_failure_preserved':True,'bounded_review':'complete CLEAR','area_status':'OPEN; installation/build/public remain future Root work'})
put('OPEN.json',{'status':'OPEN','reviewed_at':now,'bounded_source_review':'COMPLETE / CLEAR','reason':'Final strict2 bound; installation/build/public integration not claimed and area remains OPEN.','draft_sha256':results[-1]['source_sha256']})
print(json.dumps({'status':'CLEAR / OPEN','sources':len(records),'cuts':sum(len(r['cuts']) for r in records),'byte_checks':checks,'report_sha256':sha((O/'report.txt').read_bytes()),'source_index_sha256':sha((O/'source-index.json').read_bytes())},indent=2))
