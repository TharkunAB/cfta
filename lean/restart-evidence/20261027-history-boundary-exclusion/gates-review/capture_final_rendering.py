from pathlib import Path
from datetime import datetime
from zoneinfo import ZoneInfo
import hashlib,json,shutil
A=Path('/tmp/mcfta-history-boundary-exclusion-20261027');O=A/'gates-review';R=Path('/home/tritlo/Code/mcfta')
def sha(d):return hashlib.sha256(d).hexdigest()
def save(rel,d):
 p=O/rel;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(d);return {'snapshot':str(p),'bytes':len(d),'sha256':sha(d)}
def put(rel,x):return save(rel,(json.dumps(x,indent=2,ensure_ascii=False)+'\n').encode())
h=O/'review-revisions/before-final-rendering';h.mkdir(parents=True,exist_ok=True)
for n in ['source-index.json','report.txt','OPEN.json','verification.json']:
 if not (h/n).exists():shutil.copyfile(O/n,h/n)
records=json.loads((h/'source-index.json').read_text())['sources']
def capture(source,rel,spans,scope):
 p=Path(source);d=p.read_bytes();r={'source':str(p),**save(rel,d),'scope':'whole source/evidence identity','reviewed_scope':scope,'cuts':[]};records.append(r)
 for first,last,label in spans:
  assert 1<=first<=last<=len(d.splitlines(keepends=True)),(p,last);c=b''.join(d.splitlines(keepends=True)[first-1:last]);r['cuts'].append({'first_line':first,'last_line':last,**save(f'final-render-cuts/{p.stem}-{first}-{last}.txt',c),'scope':'literal cut','purpose':label})
 return d
render='SourcePruningEnumerationOutputRendering';sound='SourcePruningEnumerationHistoryRenderingSoundness'
render_source=capture(A/f'root-drafts/v3/{render}.lean',f'final-sources/{render}.lean',[(1,34,'whole actual history context'),(36,47,'original ResourceHistory→own complete Packet'),(49,78,'actual own-history render assignment with no final resource admission')],'WHOLE final80-line module read; replaces temporary v1 helper')
sound_path=A/f'root-drafts/v1/{sound}.lean';sound_lines=len(sound_path.read_bytes().splitlines())
sound_source=capture(sound_path,f'final-sources/{sound}.lean',[(1,37,'whole actual annotated history context'),(39,72,'full actual render/Discharged/original stored slot+lookup contract'),(73,sound_lines-2,'construct assignment then backward soundness and original handle readback')],f'WHOLE final{sound_lines}-line module read')
assert sha(render_source)=='8dac069396af8dd308a3812d0cf35ffaabbb1c01ec23af71f9d05422b84d4df3' and len(render_source.splitlines())==81
assert sha(sound_source)=='e292234a01a5cff0d0202fedc4b704cf6134c6b3aa5e3131d5a08e8550028ec6'
capture(R/'lean/MicroCFTA/SourcePruningEnumerationNativeLanguage.lean','final-render-inputs/SourcePruningEnumerationNativeLanguage.lean',[(18,39,'exact original native handle lookup→meaning iff')],'lines18-54 read; only actual root readback API used')
checks=[]
for check,stem,success in [('strict-output-rendering-2',render,False),('strict-output-rendering-3',render,True),('strict-history-render-soundness-1',sound,True)]:
 checked=capture(A/check/f'MicroCFTA/{stem}.lean',f'final-render-strict/{check}/{stem}.lean',[],'whole actual strict variant preserved; final sources read whole')
 report=capture(A/check/'report.json',f'final-render-strict/{check}/report.json',[],'whole actual strict report read')
 raw=capture(A/check/'raw.log',f'final-render-strict/{check}/raw.log',[],'whole actual failure/success output read')
 r=json.loads(report);assert sha(checked)==r['source_sha256'] and len(raw)==r['bytes'] and sha(raw)==r['sha256']
 assert r['cgroup_limits']=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
 assert (r['exit_code']==0)==success
 if success:assert raw==b'' and checked==(render_source if stem==render else sound_source)
 checks.append({'name':check,'source_sha256':sha(checked),'exit_code':r['exit_code'],'raw_bytes':len(raw),'raw_sha256':sha(raw)})
for rel in ['render-build-order-correction.json','build-history-meaning-rendering-1/report.json','build-history-meaning-rendering-1/raw.log','build-history-meaning-rendering-2/report.json','build-history-meaning-rendering-2/raw.log']:
 capture(A/rel,'final-render-build/'+rel,[],'actual build attempt/correction evidence read; initial missing module failure preserved, later2083-job pass verified')
for check in ['build-history-meaning-rendering-1','build-history-meaning-rendering-2']:
 r=json.loads((A/check/'report.json').read_text());raw=(A/check/'raw.log').read_bytes();assert len(raw)==r['bytes'] and sha(raw)==r['sha256'];assert r['exit_code']==(1 if check.endswith('-1') else 0)
assert b'2083 jobs' in (A/'build-history-meaning-rendering-2/raw.log').read_bytes()
assert sound_source.count(b'history.forget.render_assignment')==1 and sound_source.count(b'history.sound actualNext canonical discharged')==1
now=datetime.now(ZoneInfo('Europe/Stockholm')).isoformat()
review=f'''[{now}] CLEAR / OPEN: final history-derived output Packet and original-root rendering soundness.

WHOLE final OutputRendering81 lines / {sha(render_source)} and HistoryRenderingSoundness{sound_lines} lines / {sha(sound_source)} read. Their actual strict3 and strict1 checks respectively pass0/raw0 with memory.max/high4 GiB,swap0,all linters/warnings fatal. The prior55-line OutputResources helper stays historical TEMP only; final public OutputRendering instead derives its required own Packet directly from the actual ResourceHistory. V2 failed to infer finalMetadata's Typing; the actual failed source/log are retained. V3 has the explicit Metadata Typing binder and passes. The combined build initially failed because Root attempted it before installing the corrected rendering module; the honest correction receipt and actual failure are preserved. The subsequent combined build passes2083 jobs. No failed version is described as a pass.

ResourceHistory.output_packet inducts over the ORIGINAL resource history. Stop/done use their literal own admission Packet. Parked/ordinary use the SAME tail IH, whose output is the same final output value. The result is a complete Packet at output.caller/output.cache, with actual existential final inventory/full Memos/metadata. It does not claim an extra aggregate Post or full-Memos equality with a query field. Safe and Stratified come from that genuine Packet; no final Safety/Resources premise or Frame→Safe inference is added.

ResourceHistory.render_assignment calls the actual native renderer assignment theorem at this output's OWN native heap/cache. Its inputs are actual render Success, Discharged and checks for all returned residuals. The constructed assignment satisfies that output cache and actual returned rendered state, with term=assignment uv and the actual compression Frame. No earlier acceptance or assumed final assignment is used.

ResourceHistoryWithArity.render_sound first constructs this assignment from history.forget and the actual renderer, then applies decorated-history soundness with actualNext, initial Canonical and the same discharge. That gives Satisfies at the ORIGINAL caller heap/input cache. The ORIGINAL stored pending slot at uv supplies its handle domain and EVERY suspended Holds clause; the actual ORIGINAL lookup identifies that handle's native value. Rewriting term=assignment uv derives original native value acceptance and suspended Holds of this actual rendered term. Output cache/rendered-state Satisfies and Frame remain the same witnesses. This does not substitute a desired original acceptance premise or an old renderer success.

No source blocker found. The new original-root result remains conditional on the COMPLETE numeric-arity-decorated actual history. The checked-build helper can discharge a local annotation from actual provenance; global construction of all such path decorations from the bare finite producer is still OPEN. Coverage and physical Haskell correspondence are not claimed. Final finite-producer conditional observer, public/Audit and documents remain pending before sealing. All earlier failed/temporary stages and frozen areas remain preserved.
'''
save('final-rendering-review.txt',review.encode());save('report.txt',(h/'report.txt').read_bytes()+b'\n'+review.encode())
put('final-rendering-check.json',{'status':'CLEAR','reviewed_at':now,'sources':{'OutputRendering':{'sha256':sha(render_source),'lines':81},'HistoryRenderingSoundness':{'sha256':sha(sound_source),'lines':sound_lines}},'strict_attempts':checks,'final_packet_derived_from_original_history':True,'constructed_assignment_not_assumed':True,'original_stored_lookup_and_all_suspended_holds_retained':True,'pathwise_arity_decoration_origin_still_open':True,'build_order_failure_preserved':True})
put('source-index.json',{'schema':'whole sources and explicit literal cuts','cut_convention':'one-based inclusive lines; splitlines(keepends=True); original LF retained','sources':records})
put('OPEN.json',{'status':'OPEN','reviewed_at':now,'current_review':'CLEAR decorated history backward language and actual original-root rendering','reason':'Await exact finite producer conditional observer and final source/public/Audit/document claims.','publication_outcome':'not asserted'})
count=0
for rec in records:
 d=Path(rec['source']).read_bytes();assert d==Path(rec['snapshot']).read_bytes() and len(d)==rec['bytes'] and sha(d)==rec['sha256'];count+=1
 for c in rec['cuts']:
  x=b''.join(d.splitlines(keepends=True)[c['first_line']-1:c['last_line']]);assert x==Path(c['snapshot']).read_bytes() and len(x)==c['bytes'] and sha(x)==c['sha256'];count+=1
put('verification.json',{'status':'PASS','checked_at':now,'source_records':len(records),'cuts':sum(len(x['cuts']) for x in records),'byte_checks':count,'bundle_status':'OPEN'})
print(json.dumps({'status':'CLEAR / OPEN','report_sha256':sha((O/'report.txt').read_bytes()),'source_index_sha256':sha((O/'source-index.json').read_bytes()),'source_records':len(records),'cuts':sum(len(x['cuts']) for x in records),'byte_checks':count,'history_render_lines':sound_lines},indent=2))
