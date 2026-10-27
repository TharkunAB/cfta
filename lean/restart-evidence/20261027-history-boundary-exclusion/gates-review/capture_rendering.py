from pathlib import Path
from datetime import datetime
from zoneinfo import ZoneInfo
import hashlib,json,shutil
A=Path('/tmp/mcfta-history-boundary-exclusion-20261027');O=A/'gates-review';R=Path('/home/tritlo/Code/mcfta')
def sha(d):return hashlib.sha256(d).hexdigest()
def save(rel,d):
 p=O/rel;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(d);return {'snapshot':str(p),'bytes':len(d),'sha256':sha(d)}
def put(rel,x):return save(rel,(json.dumps(x,indent=2,ensure_ascii=False)+'\n').encode())
h=O/'review-revisions/before-rendering';h.mkdir(parents=True,exist_ok=True)
for n in ['source-index.json','report.txt','OPEN.json','verification.json']:
 if not (h/n).exists():shutil.copyfile(O/n,h/n)
records=json.loads((h/'source-index.json').read_text())['sources']
def capture(source,rel,spans,scope):
 p=Path(source);d=p.read_bytes();r={'source':str(p),**save(rel,d),'scope':'whole source/evidence identity','reviewed_scope':scope,'cuts':[]};records.append(r)
 for first,last,label in spans:
  assert 1<=first<=last<=len(d.splitlines(keepends=True));c=b''.join(d.splitlines(keepends=True)[first-1:last]);r['cuts'].append({'first_line':first,'last_line':last,**save(f'rendering-cuts/{p.stem}-{first}-{last}.txt',c),'scope':'literal cut','purpose':label})
 return d
name='SourcePruningEnumerationOutputRendering';expected='c1fe9ca2832986cc29e551f21cd6cf428a9576089b2a9fe1ff285a15cbf6ed0e'
source=capture(A/f'root-drafts/v1/{name}.lean',f'whole/{name}.lean',[(1,19,'whole module context'),(21,46,'complete own-output rendering contract'),(47,54,'own Packet safe/order extraction and one actual render theorem call')],'whole55-line source read')
assert sha(source)==expected and len(source.splitlines())==55
inputs=[('SourcePruningEnumerationOutcomeResources',[(43,54,'complete own-output resource definition')],'lines22-57 read; own Packet/full native endpoint premise checked'),('SourcePruningEnumerationRendering',[(22,26,'exact structural discharge'),(142,157,'entire existing native assignment theorem contract')],'lines18-30 and140-180 read; focused use is assignment API'),('SourcePruningEnumerationOrdinaryReceiptLanguage',[(93,157,'lower callback input law has independent scanInventory and actual full scanMemos')],'lines24-166 read; exact inventory separation inspected'),('SourcePruningEnumerationPrefixLanguage',[(195,216,'actual prefix semantics uses current original inventory and returns concrete PrefixMeaning')],'lines195-235 read; focused header inspected'),('SourceFlatPruningRecursiveOutputRendering',[(1,51,'existing flat own-output counterpart and its own-cache relation')],'whole source read; counterpart has generic holds/meaning and stronger flat after equality')]
for stem,spans,scope in inputs:capture(R/f'lean/MicroCFTA/{stem}.lean',f'rendering-inputs/{stem}.lean',spans,scope)
checked=capture(A/f'strict-output-rendering-1/MicroCFTA/{name}.lean',f'rendering-strict/{name}.lean',[],'whole actual strict source equals reviewed draft')
report=capture(A/'strict-output-rendering-1/report.json','rendering-strict/report.json',[],'whole actual first strict report read')
raw=capture(A/'strict-output-rendering-1/raw.log','rendering-strict/raw.log',[],'whole empty actual strict output read')
r=json.loads(report);assert checked==source and r['source_sha256']==expected and r['exit_code']==0 and r['bytes']==len(raw)==0 and r['sha256']==sha(raw)
assert r['cgroup_limits']=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
now=datetime.now(ZoneInfo('Europe/Stockholm')).isoformat()
review=f'''[{now}] CLEAR / OPEN: own-output rendering helper and exact inventory boundary.

WHOLE SourcePruningEnumerationOutputRendering55 lines / {expected} read. Actual strict-output-rendering-1 FIRST PASS0/raw0, exact checked source, memory.max/high4 GiB and swap0 verified. The wrapper extracts the actual own-output Packet from OutputResources, then its Safe and Stratified witnesses. It calls the existing native render_assignment ONCE with exactly output.caller.heap, output.cache.core, actual render uv/term/pending/after, Discharged and checks for every returned residual. It constructs an assignment satisfying that own cache, term=assignment uv, the actual compression Frame, and Satisfies after. It does not derive Safe from Frame or earlier-input acceptance. Native Frame is retained as the actual result; the flat counterpart's after=before equality is not asserted for this native worker.

Inventory boundary. The earlier selected checked-output theorem preserves its ENTIRE old local contract, including enteredPacket indexed by the original selected inventory. Actual ResourceHistory's narrowed ordinary step instead retains its reached ordinaryInventory/ordinaryMemos after prefix Post. Those inventories cannot be equated by a generic rebase or query equality. The existing lower CompletedHeadReceipt.sound_ordinary_callback_input has an independent scanInventory/scanCaller/FULL scanMemos and derives its head relation through the actual aggregate Post. PrefixLanguage.prefix_semantics separately handles the original selected input and reached narrowed cache. Composing those lower laws is the correct planned whole-history route. The local selected wrapper remains valid under its stated conditional inventory premise; it is not being advertised as the direct whole-history consumer.

No source blocker found. Whole-history backward language and its rendering corollary are pending actual source review and strict receipts. The remaining checked-origin transport for every actual head remains explicit. No per-step semantic implication, desired assignment, Canonical from Packet, or future runtime success is introduced by this helper. Keep the review OPEN for whole-history/final source/build/public/Audit/document claims. Earlier frozen areas remain untouched.
'''
save('rendering-review.txt',review.encode());save('report.txt',(h/'report.txt').read_bytes()+b'\n'+review.encode())
put('rendering-check.json',{'status':'CLEAR','reviewed_at':now,'source_sha256':expected,'strict_exit_code':0,'strict_raw_bytes':0,'own_output_heap_cache_uv_residuals_retained':True,'actual_frame_not_safe_source':True,'earlier_input_acceptance_claim':False,'inventory_boundary':'Local selected API fixed-inventory premise differs from actual post-prefix ordinaryInventory; use lower prefix+ordinary laws, no rebase.'})
put('source-index.json',{'schema':'whole sources and explicit literal cuts','cut_convention':'one-based inclusive lines; splitlines(keepends=True); original LF retained','sources':records})
put('OPEN.json',{'status':'OPEN','reviewed_at':now,'current_review':'CLEAR arity, retention, local selected integration and own-output rendering','reason':'Await actual whole-history proof and final source/build/public/Audit/document claims.','publication_outcome':'not asserted'})
checks=0
for rec in records:
 d=Path(rec['source']).read_bytes();assert d==Path(rec['snapshot']).read_bytes() and len(d)==rec['bytes'] and sha(d)==rec['sha256'];checks+=1
 for c in rec['cuts']:
  x=b''.join(d.splitlines(keepends=True)[c['first_line']-1:c['last_line']]);assert x==Path(c['snapshot']).read_bytes() and len(x)==c['bytes'] and sha(x)==c['sha256'];checks+=1
put('verification.json',{'status':'PASS','checked_at':now,'source_records':len(records),'cuts':sum(len(x['cuts']) for x in records),'byte_checks':checks,'bundle_status':'OPEN'})
print(json.dumps({'status':'CLEAR / OPEN','report_sha256':sha((O/'report.txt').read_bytes()),'source_index_sha256':sha((O/'source-index.json').read_bytes()),'source_records':len(records),'cuts':sum(len(x['cuts']) for x in records),'byte_checks':checks},indent=2))
