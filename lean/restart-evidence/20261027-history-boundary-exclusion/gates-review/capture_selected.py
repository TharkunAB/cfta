from pathlib import Path
from datetime import datetime
from zoneinfo import ZoneInfo
import hashlib,json,shutil
A=Path('/tmp/mcfta-history-boundary-exclusion-20261027');O=A/'gates-review';R=Path('/home/tritlo/Code/mcfta')
def sha(d):return hashlib.sha256(d).hexdigest()
def save(rel,d):
 p=O/rel;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(d);return {'snapshot':str(p),'bytes':len(d),'sha256':sha(d)}
def put(rel,x):return save(rel,(json.dumps(x,indent=2,ensure_ascii=False)+'\n').encode())
h=O/'review-revisions/before-selected';h.mkdir(parents=True,exist_ok=True)
for n in ['source-index.json','report.txt','OPEN.json','verification.json']:
 if not (h/n).exists():shutil.copyfile(O/n,h/n)
records=json.loads((h/'source-index.json').read_text())['sources']
def capture(source,rel,spans,scope):
 p=Path(source);d=p.read_bytes();r={'source':str(p),**save(rel,d),'scope':'whole source/evidence identity','reviewed_scope':scope,'cuts':[]};records.append(r)
 for first,last,label in spans:
  assert 1<=first<=last<=len(d.splitlines(keepends=True));c=b''.join(d.splitlines(keepends=True)[first-1:last]);r['cuts'].append({'first_line':first,'last_line':last,**save(f'selected-cuts/{p.stem}-{first}-{last}.txt',c),'scope':'literal cut','purpose':label})
 return d
name='SourcePruningEnumerationSelectedCheckedOutputLanguage';expected='19119237da5c35f2110df46141579ca8f16f57b82c15c8e92aefa44c5e282aaa'
new=capture(A/f'selected-checked-output-draft/{name}.lean',f'whole/{name}.lean',[(1,30,'module context'),(32,85,'complete original admission retained through invocation'),(86,116,'actual checked provenance and own-output tail replace only two old gates'),(117,137,'entire unchanged old semantic conclusion'),(138,154,'one arity helper, one retention helper, one original semantic consumer')],'whole156-line module read')
assert sha(new)==expected and len(new.splitlines())==156
old=capture(R/'lean/MicroCFTA/SourcePruningEnumerationSelectedInvocationLanguage.lean','selected-inputs/SourcePruningEnumerationSelectedInvocationLanguage.lean',[(31,95,'entire old theorem admission through freshArity/retained'),(96,114,'entire old semantic conclusion'),(115,124,'actual metadata/nonterminal derived and old consumer call')],'whole original126-line module read')
checked=capture(A/f'strict-selected-checked-output-1/MicroCFTA/{name}.lean',f'selected-strict/{name}.lean',[],'whole actual strict source byte-equal to reviewed draft')
report=capture(A/'strict-selected-checked-output-1/report.json','selected-strict/report.json',[],'whole actual first strict report read')
raw=capture(A/'strict-selected-checked-output-1/raw.log','selected-strict/raw.log',[],'whole actual empty strict log read')
r=json.loads(report);assert new==checked and r['source_sha256']==expected and r['exit_code']==0 and r['bytes']==len(raw)==0 and r['sha256']==sha(raw)
assert r['cgroup_limits']=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
def head(data,name):
 first=data.index(('theorem '+name+'\n').encode());last=data.index(b' := by\n',first);return data[first:last]
oh=head(old,'narrowed_receipt_sound_of_invocation');nh=head(new,'narrowed_receipt_sound_of_invocation_checked_output')
conclusion_marker='    ∃ (handle : Nat)'.encode();old_conclusion_start=oh.index(conclusion_marker);new_conclusion_start=nh.index(conclusion_marker)
oc=oh[old_conclusion_start:];nc=nh[new_conclusion_start:];assert oc==nc
old_gates_start=oh.index(b'    (freshArity : ');replacement_start=nh.index(b'    (sourceSymbol : Symbol)')
old_gates=oh[old_gates_start:old_conclusion_start];replacement=nh[replacement_start:new_conclusion_start]
recovered=(nh[:replacement_start]+old_gates+nc).replace(b'theorem narrowed_receipt_sound_of_invocation_checked_output\n',b'theorem narrowed_receipt_sound_of_invocation\n',1)
assert recovered==oh
for label,d in [('old-header',oh),('new-header',nh),('recovered-old-header',recovered),('old-conclusion',oc),('new-conclusion',nc),('only-old-gates-replaced',old_gates),('replacement-actual-provenance-and-output',replacement)]:save(f'selected-contracts/{label}.txt',d)
assert new.count(b'  exact narrowed_receipt_sound_of_invocation\n')==1
assert new.count(b':= SourcePruningEnumerationNativeHookResources.CompletedHeadReceipt.freshArity_of_checked_build')==1
assert new.count(b':= SourcePruningEnumerationOpaqueEvent.completed_head_output_retained')==1
comparison={'status':'PASS','new_source_sha256':expected,'old_source_sha256':sha(old),'full_old_header_recovered_literal':True,'old_header_bytes':len(oh),'old_header_sha256':sha(oh),'recovered_old_header_sha256':sha(recovered),'entire_old_conclusion_literal':True,'old_conclusion_bytes':len(oc),'old_conclusion_sha256':sha(oc),'new_conclusion_sha256':sha(nc),'mapping':['Restore original theorem name.','Replace only actual checked-build/Post/identity + false callback/tail/discharged block with original freshArity and retained binders.'],'all_other_old_inputs_retained':True,'original_semantic_consumer_calls':1,'checked_arity_helper_calls':1,'same_output_retention_helper_calls':1}
put('selected-contract-comparison.json',comparison)
# Retain the independent author comparison without relying on it for our equality check.
capture(A/'selected-checked-output-draft/contract-comparison.json','selected-contracts/author-comparison.json',[],'whole author comparison read and independently reproduced')
now=datetime.now(ZoneInfo('Europe/Stockholm')).isoformat()
review=f'''[{now}] CLEAR / OPEN: exact selected semantic integration.

WHOLE new SourcePruningEnumerationSelectedCheckedOutputLanguage156 lines / {expected} reviewed. Actual strict-selected-checked-output-1 is a byte-identical FIRST PASS/raw0 under memory.max/high4 GiB,swap0,all linters/warnings fatal. No build/Lean/Git/network/board action was run here.

The ENTIRE old SelectedInvocationLanguage theorem header is independently recovered LITERALLY: {len(oh)} bytes / {sha(oh)}. Only the theorem name changes and ONLY old freshArity/retained binders are replaced with actual past checked-build/Post/identity provenance and actual singleton false callback/SAME tail/output Discharged inputs. Every other old input, including initial Canonical, recording Success, actual entry/invocation and full Packet/Memos receipts, is retained in its old order. The ENTIRE old conclusion is byte-identical: {len(oc)} bytes / {sha(oc)}. The author comparison is retained separately; our check reproduces it from exact source bytes.

The arity helper receives the literal entered cache/counter, actual head Caller/full Memos/updated metadata/CompletedHeadReceipt, original constructed edge, built heap/caller/Post and matching identity. Its derived fresh arity concerns this exact edge. The retention helper receives the SAME receipt, actual false callback return, SAME full returned Memos/recorded metadata/framed cache and literal restart ResourceHistory, and the OWN output Discharged premise. It derives the full forall-project child-retention gate at entered.counter. The old semantic consumer is called ONCE with both derived gates. No helper chooses an unrelated head, entry or callback endpoint.

No Satisfies premise is added to the theorem input. Satisfies at the actual callbackAfter remains the antecedent of the unchanged universal backward-law CONCLUSION. The result still returns actual captured-slot/source-parent receipts, original-input Satisfies, own edge/parent native acceptance, all inherited Holds and filled-fragment identity under that implication. It does not manufacture an assignment, assert every output is discharged, derive checked provenance from Packet alone, or transfer caches across siblings.

No source blocker found. This closes the two explicit local semantic gates when the stated actual constructor/history/output receipts are provided. A whole ResourceHistory soundness consumer and global derivation of checked origins for every current edge remain separate. Keep this bundle OPEN for their actual sources plus final build/public/Audit/document claim evidence. Earlier phase reports and exact comparisons are preserved; previous frozen areas were not changed.
'''
save('selected-review.txt',review.encode());save('report.txt',(h/'report.txt').read_bytes()+b'\n'+review.encode())
put('source-index.json',{'schema':'whole sources and explicit literal cuts','cut_convention':'one-based inclusive lines; splitlines(keepends=True); original LF retained','sources':records})
put('OPEN.json',{'status':'OPEN','reviewed_at':now,'current_review':'CLEAR arity, discharged retention and exact selected semantic integration','reason':'Await whole-history soundness source and final source/build/public/Audit/document claims.','publication_outcome':'not asserted'})
checks=0
for rec in records:
 d=Path(rec['source']).read_bytes();assert d==Path(rec['snapshot']).read_bytes() and len(d)==rec['bytes'] and sha(d)==rec['sha256'];checks+=1
 for c in rec['cuts']:
  x=b''.join(d.splitlines(keepends=True)[c['first_line']-1:c['last_line']]);assert x==Path(c['snapshot']).read_bytes() and len(x)==c['bytes'] and sha(x)==c['sha256'];checks+=1
put('verification.json',{'status':'PASS','checked_at':now,'source_records':len(records),'cuts':sum(len(x['cuts']) for x in records),'byte_checks':checks,'full_old_header_and_conclusion_literal':True,'bundle_status':'OPEN'})
print(json.dumps({'status':'CLEAR / OPEN','report_sha256':sha((O/'report.txt').read_bytes()),'source_index_sha256':sha((O/'source-index.json').read_bytes()),'source_records':len(records),'cuts':sum(len(x['cuts']) for x in records),'byte_checks':checks,'old_header_bytes':len(oh),'old_conclusion_bytes':len(oc)},indent=2))
