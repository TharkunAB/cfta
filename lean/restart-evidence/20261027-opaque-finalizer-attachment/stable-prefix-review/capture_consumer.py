from pathlib import Path
from datetime import datetime
from zoneinfo import ZoneInfo
import hashlib,json,shutil
AREA=Path('/tmp/mcfta-opaque-finalizer-attachment-20261027');OUT=AREA/'stable-prefix-review';REPO=Path('/home/tritlo/Code/mcfta')
def sha(d):return hashlib.sha256(d).hexdigest()
def save(rel,d):
 p=OUT/rel;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(d)
 return {'snapshot':str(p),'bytes':len(d),'sha256':sha(d)}
def put(rel,x):return save(rel,(json.dumps(x,indent=2,ensure_ascii=False)+'\n').encode())
history=OUT/'review-revisions/pre-output';history.mkdir(parents=True,exist_ok=True)
for name in ['source-index.json','report.txt','OPEN.json','verification.json']:
 if not (history/name).exists():shutil.copyfile(OUT/name,history/name)
records=json.loads((history/'source-index.json').read_text())['sources']
def capture(source,rel,spans,scope):
 p=Path(source);d=p.read_bytes();lines=d.splitlines(keepends=True)
 r={'source':str(p),**save(rel,d),'scope':'whole source/evidence input','reviewed_scope':scope,'cuts':[]}
 for first,last,label in spans:
  assert 1<=first<=last<=len(lines),(p,first,last,len(lines))
  c=b''.join(lines[first-1:last]);r['cuts'].append({'first_line':first,'last_line':last,**save(f'consumer-cuts/{p.stem}-{first}-{last}.txt',c),'scope':'literal cut','purpose':label})
 records.append(r);return d
stem='SourcePruningEnumerationOpaqueOutputAttachment'
source=capture(REPO/f'lean/MicroCFTA/{stem}.lean',f'final-sources/{stem}.lean',[(1,28,'whole module context and imports'),(30,69,'full actual receipt/callback/tail admission and own-output conclusion'),(70,84,'one head call, actual callback frame and same tail history')],'whole final installed 86-line module read')
assert sha(source)=='5255b78cbf45c0be30060b9cc0f754e7e10ac9717eccad66475edd8968921896'
for name,first,last,label in [('SourcePruningEnumerationHistoryBoundaryIsolation',26,136,'actual decision alignment and full own-output boundary persistence'),('SourcePruningEnumerationIsolationReads',77,90,'actual recordTypes Success to compression frame'),('SourcePruningEnumerationFiniteHistoryContract',45,132,'actual ordinary full head receipt and full admitted history operation tags')]:
 capture(REPO/f'lean/MicroCFTA/{name}.lean',f'consumer-inputs/{name}.lean',[(first,last,label)],'whole boundary module read / focused allocation, callback and history definitions read as recorded cuts')
checks=[]
for attempt in [1,2,3]:
 check=f'strict-output-attachment-{attempt}'
 checked=capture(AREA/check/f'MicroCFTA/{stem}.lean',f'consumer-checks/{check}/{stem}.lean',[],'whole historical checked source identity retained; final variant independently read')
 report=capture(AREA/check/'report.json',f'consumer-checks/{check}/report.json',[],'whole actual strict report read')
 raw=capture(AREA/check/'raw.log',f'consumer-checks/{check}/raw.log',[],'whole actual strict output read')
 r=json.loads(report);assert sha(checked)==r['source_sha256'] and len(raw)==r['bytes'] and sha(raw)==r['sha256']
 assert r['cgroup_limits']=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
 checks.append({'attempt':attempt,'exit_code':r['exit_code'],'source_sha256':sha(checked),'raw_bytes':len(raw),'raw_sha256':sha(raw)})
 if attempt==3:assert checked==source and r['exit_code']==0 and raw==b''
 else:assert r['exit_code']==1 and sha(checked)=='00aca89fd6df9e8d60054248b6257ff39d9b1e285a2397718e5131e3f96bb537'
capture(AREA/'output-check-path-correction.json','consumer-checks/output-check-path-correction.json',[],'whole actual wrong-v1-path correction read; attempt2 is retained as failure')
# Exact installed bytes for both already reviewed producers.
for name,expected in [('SourcePruningEnumerationOpaqueStablePrefixResources','60806a2783eb4988013b5089f5414ebdbb19c25bdf09828efd2ebdc6a9849434'),('SourcePruningEnumerationOpaqueFinalizerAttachment','7c4ce6fa84d85da5e599fcf491b8ffd3f0aa8179c886eae429af6480104429af')]:
 d=capture(REPO/f'lean/MicroCFTA/{name}.lean',f'installed-sources/{name}.lean',[],'installed source byte-equal to final documented reviewed source')
 assert sha(d)==expected and d==(OUT/f'final-sources/{name}.lean').read_bytes()
for rel in ['modules.json','public-declarations.json','public-definitions.json','build-aggregate-final/report.json','build-aggregate-final/raw.log','strict-audit-final-1/report.json','strict-audit-final-1/raw.log']:
 if (AREA/rel).exists():capture(AREA/rel,'checkpoint-evidence/'+rel,[],'whole current source/build/Audit metadata or raw output read; final public evidence pending')
assert source.count(b':= completed_head_opaque_isolated')==1
put('consumer-comparison.json',{'status':'PASS','installed_source_sha256':sha(source),'line_count':len(source.splitlines()),'head_attachment_calls':1,'actual_false_callback_row':True,'same_returned_inventory_caller_full_memos_metadata_framed_cache':True,'tail_decision_literal_restart':True,'own_output_cache_and_heap_in_conclusion':True,'strict_attempts':checks,'attempt2_status':'wrong path repeated v1 failure; no false claim that corrected v2 failed','completion_scope':'local consumer of actual head, callback and tail receipts; not a new completion producer'})
put('source-index.json',{'schema':'whole sources and explicit literal cuts','cut_convention':'one-based inclusive lines; splitlines(keepends=True); original LF bytes retained','sources':records})
now=datetime.now(ZoneInfo('Europe/Stockholm')).isoformat()
save('consumer-review.txt',f'''[{now}] CLEAR / OPEN for final output consumer {sha(source)}.

The whole installed 86-line module and actual strict3 source/report/raw were read. The checked and installed sources match exactly. Strict3 passes with empty raw output under memory.max/high 4 GiB and swap.max 0. Attempts1 and2 both checked the original 00aca89f source and failed on unresolved lookupNode. The wrong-path correction for attempt2 is retained. Corrected v2 was checked only by attempt3; it passed. No failed attempt is omitted or represented as a pass.

The theorem keeps the explicit actual CompletedHeadReceipt and projection/location/boundary/nonterminal gates. It adds an actual singleton false recordTypes observation at that same headCache plus ResourceHistory from its exact framed callback cache. The tail uses returnedInventory, reached Caller, FULL returnedMemos, actual recorded metadata, its own seed/ceiling, and the literal Restart.decision. These are concrete observation/trace premises of a local consumer. The theorem is not a new producer from bare initial inputs or a claim that every output has an opaque event.

The head attachment is called once and derives its own reached-heap lookup and head-cache isolation. Actual callback Success follows from the supplied complete singleton raw equality. The existing recordTypes_frame uses genuine Total from head.completed.safe, so isolation transports through that actual callback core; Frame never supplies Safe. Boundary persistence then consumes this SAME actual tail ResourceHistory and literal restart decision. Its induction retains native Post lookup at each own caller. The returned marker isolation, native lookup and notDischarged refer to the SAME emitted output.cache/output.caller. No sibling cache transfer or query-to-full-Memos equality is asserted.

No source issue was found. This closes the local actual head→false callback→own tail output structural marker attachment. It does not prove full assignment acceptance/coverage, physical Haskell correspondence, or that unrelated sibling outputs contain the marker. Public/Audit/document claim review remains pending; the combined bundle stays OPEN.
'''.encode())
put('OPEN.json',{'status':'OPEN','reviewed_at':now,'review_result':'CLEAR','reason':'Final public/Audit/document-validation claims are still required before sealing.','reviewed_output_source_sha256':sha(source),'publication_status':'not evaluated or predicted'})
print(json.dumps({'status':'CLEAR / OPEN','consumer_report_sha256':sha((OUT/'consumer-review.txt').read_bytes()),'source_index_sha256':sha((OUT/'source-index.json').read_bytes()),'whole_records':len(records),'cuts':sum(len(r['cuts']) for r in records)},indent=2))
