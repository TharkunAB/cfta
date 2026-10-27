from pathlib import Path
from datetime import datetime
from zoneinfo import ZoneInfo
import hashlib,json,shutil
A=Path('/tmp/mcfta-history-boundary-exclusion-20261027');O=A/'gates-review';R=Path('/home/tritlo/Code/mcfta')
def sha(d):return hashlib.sha256(d).hexdigest()
def save(rel,d):
 p=O/rel;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(d);return {'snapshot':str(p),'bytes':len(d),'sha256':sha(d)}
def put(rel,x):return save(rel,(json.dumps(x,indent=2,ensure_ascii=False)+'\n').encode())
h=O/'review-revisions/before-history';h.mkdir(parents=True,exist_ok=True)
for n in ['source-index.json','report.txt','OPEN.json','verification.json']:
 if not (h/n).exists():shutil.copyfile(O/n,h/n)
records=json.loads((h/'source-index.json').read_text())['sources']
def capture(source,rel,spans,scope):
 p=Path(source);d=p.read_bytes();r={'source':str(p),**save(rel,d),'scope':'whole source/evidence identity','reviewed_scope':scope,'cuts':[]};records.append(r)
 for first,last,label in spans:
  assert 1<=first<=last<=len(d.splitlines(keepends=True)),(p,last);c=b''.join(d.splitlines(keepends=True)[first-1:last]);r['cuts'].append({'first_line':first,'last_line':last,**save(f'history-cuts/{p.stem}-{first}-{last}.txt',c),'scope':'literal cut','purpose':label})
 return d
name='SourcePruningEnumerationResourceHistoryMeaning';expected='c58639b3bdfff2ce324ebe54ab60ae856f7d147596e6f5957c435f97d5e0b08d'
source=capture(A/'history-meaning-draft/revisions/v2.lean',f'whole/{name}.lean',[(1,53,'complete ordinary receipt plus ONLY numeric arity'),(55,124,'all complete original operation/history tags with decorated receipt'),(127,171,'both forget maps and exact endpoints'),(173,242,'whole backward proof through all constructors and actual inventories')],'WHOLE244-line authoritative v2 source read')
assert sha(source)==expected and len(source.splitlines())==244
old=capture(R/'lean/MicroCFTA/SourcePruningEnumerationFiniteHistoryContract.lean','history-inputs/SourcePruningEnumerationFiniteHistoryContract.lean',[(45,132,'complete old ordinary receipt and original operation tags')],'exact old definition spans reviewed previously and independently compared byte-for-byte now; full identity retained')
for stem,spans,scope in [
 ('SourcePruningEnumerationHistoryReceiptCanonical',[(33,64,'actual entry/head/callback Canonical preservation')],'lines30-74 read; actual-operation Canonical route verified'),
 ('SourcePruningEnumerationParkedMarkerAttachment',[(49,81,'actual parked prefix and SAME tail excludes output discharge'),(82,135,'actual read/check/restart/isolated-boundary transport')],'lines49-137 read; whole parked branch derivation inspected'),
 ('SourcePruningEnumerationPrefixCanonicalHistory',[(108,127,'initial Canonical+actual PrefixValid→retained current cache Canonical')],'lines108-142 read; full identity retained')]:capture(R/f'lean/MicroCFTA/{stem}.lean',f'history-inputs/{stem}.lean',spans,scope)
checks=[];first_source=None
for attempt in [1,2]:
 check=f'strict-resource-history-meaning-{attempt}'
 checked=capture(A/check/f'MicroCFTA/{name}.lean',f'history-strict/{check}/{name}.lean',[],'whole actual checked variant retained; v2 authoritative source read whole')
 report=capture(A/check/'report.json',f'history-strict/{check}/report.json',[],'whole actual strict report read')
 raw=capture(A/check/'raw.log',f'history-strict/{check}/raw.log',[],'whole actual failure/success raw output read')
 r=json.loads(report);assert sha(checked)==r['source_sha256'] and len(raw)==r['bytes'] and sha(raw)==r['sha256']
 assert r['cgroup_limits']=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
 if attempt==1:
  assert r['exit_code']==1;first_source=checked
 else:assert r['exit_code']==0 and raw==b'' and checked==source
 checks.append({'attempt':attempt,'exit_code':r['exit_code'],'source_sha256':sha(checked),'raw_bytes':len(raw),'raw_sha256':sha(raw)})
assert source.replace(b'local notation "Fragment" => Fragments.Fragment Symbol\n',b'',1)==first_source
assert b'sorry' not in source

def declaration(data,start):
 first=data.index(start);last=data.index(b'\n\n/--',first);return data[first:last]
ordinary_old=declaration(old,b'def OrdinaryHistoryReceipt\n');ordinary_new=declaration(source,b'def OrdinaryHistoryArityReceipt\n')
kept,_=ordinary_new.rsplit(' ∧\n    ∀ tries residual,'.encode(),1)
ordinary_recovered=kept.replace(b'def OrdinaryHistoryArityReceipt\n',b'def OrdinaryHistoryReceipt\n',1)
history_old=declaration(old,b'inductive ResourceHistory\n');history_new=declaration(source,b'inductive ResourceHistoryWithArity\n')
history_recovered=history_new.replace(b'ResourceHistoryWithArity',b'ResourceHistory').replace(b'OrdinaryHistoryArityReceipt',b'OrdinaryHistoryReceipt')
assert ordinary_old==ordinary_recovered and history_old==history_recovered
for tag,d in [('ordinary-original',ordinary_old),('ordinary-with-arity',ordinary_new),('ordinary-recovered',ordinary_recovered),('history-original',history_old),('history-with-arity',history_new),('history-recovered',history_recovered)]:save(f'history-contracts/{tag}.lean',d)
put('history-contract-comparison.json',{'status':'PASS','ordinary_full_original_bytes':len(ordinary_old),'ordinary_full_original_sha256':sha(ordinary_old),'ordinary_recovery_literal':True,'history_full_original_bytes':len(history_old),'history_full_original_sha256':sha(history_old),'history_recovery_literal':True,'whitespace_normalization':False,'mapping':['Remove only appended projected numeric own-arity conjunction.','Restore declaration/recursive names.'],'all_original_admission_execution_resource_and_memo_fields_retained':True,'v1_to_v2_only_added_Fragment_notation':True,'strict_attempts':checks})
capture(A/'history-meaning-draft/contract-comparison.json','history-contracts/author-comparison.json',[],'whole author comparison read; all byte equalities independently reproduced')
now=datetime.now(ZoneInfo('Europe/Stockholm')).isoformat()
review=f'''[{now}] CLEAR / OPEN: conditional whole actual resource-history backward meaning.

WHOLE authoritative ResourceHistoryMeaning v2,244 lines / {expected} read. Actual strict-resource-history-meaning-2 passes0/raw0 under memory.max/high4 GiB,swap0,all linters/warnings fatal. The complete v1 failed source/report/raw are preserved. V1 lacks the local Fragment notation, producing type mismatches and consequent declaration-uses-sorry errors. Adding only that notation recovers v2 exactly. Final v2 contains no sorry token and is the only authoritative successful variant.

Literal original-contract recovery is independently verified with NO whitespace normalization. OrdinaryHistoryArityReceipt is the ENTIRE1,588-byte original OrdinaryHistoryReceipt / {sha(ordinary_old)}, plus only forall projected tries numeric fresh own arity. ResourceHistoryWithArity recovers the ENTIRE6,242-byte original ResourceHistory / {sha(history_old)} after only name substitutions. All original admissions, actual PrefixValid/run equations, native aggregate Post/FULL Memos, actual invocation/entry/completed head, callback admission, false singleton, actual callback cache, literal Restart.decision, resources, output and stop/done tags remain. Both forget maps return the exact same old endpoints/bounds/output, using constructor induction without rerunning any producer.

The soundness contract explicitly requires a decorated history, actualNext equality to the real restart decision, initial Canonical and Discharged at its OWN output cache. Its conclusion is forall ambient/assignment, output-own-heap Satisfies implies original-input-heap Satisfies. It assumes no desired per-step semantic implication as a history annotation, no universal Ranges, no final Canonical or assignment existence. The only added path annotation is numeric own arity.

All constructors are checked. Stop/done preserve the exact original state/caller and use the supplied assignment directly. The parked branch's actual prefix and SAME forgotten tail retain their created marker at this own output; its notDischarged contradicts the supplied discharge, without a lost-suspension semantic assumption. The ordinary branch derives narrowed Canonical from the actual PrefixValid and original Canonical, then callback Canonical from real entry/completed-head/recordTypes receipts. The IH applies to that SAME actual framed callback cache, returned caller/FULL Memos/recorded metadata and literal restart decision; it receives the same own-output discharge.

The original Packet plus actual selected decision derives Ready. The exact prefix semantics gives original-to-narrowed backward meaning. Actual invocation plus actual entry derives inherited nonterminality. The same head/false callback/SAME tail and Discharged derive the complete retained-child gate. Numeric own arity is read from that exact decorated head receipt. The lower sound_ordinary_callback_input is instantiated with ACTUAL ordinaryInventory/ordinaryCaller/FULL ordinaryMemos from the post-prefix receipt, and the local aggregate head Post. It returns narrowed satisfaction, which prefix_semantics transports to the original input. No inventory rebase or equality of full Memos from query equality is used. The earlier fixed-inventory selected wrapper remains only its original local conditional theorem; this history proof correctly bypasses that premise.

No blocker found. The result proves whole recorded-path backward assignment meaning under the explicit pathwise numeric arity certificate. It does NOT derive all such annotations from bare Packet or the old finite producer. Creating the full decoration from actual checked construction/intersection origins at every current edge remains OPEN. Therefore no bare-producer all-output acceptance/coverage or physical Haskell correctness is claimed. A final rendering/history corollary and final source/public/Audit/document scope still need review before this bundle is sealed.
'''
save('history-review.txt',review.encode());save('report.txt',(h/'report.txt').read_bytes()+b'\n'+review.encode())
put('source-index.json',{'schema':'whole sources and explicit literal cuts','cut_convention':'one-based inclusive lines; splitlines(keepends=True); original LF retained','sources':records})
put('OPEN.json',{'status':'OPEN','reviewed_at':now,'current_review':'CLEAR all local gates, own-output renderer and full decorated-history backward meaning','reason':'Await final render/history corollary and final source/public/Audit/document claims.','publication_outcome':'not asserted'})
count=0
for rec in records:
 d=Path(rec['source']).read_bytes();assert d==Path(rec['snapshot']).read_bytes() and len(d)==rec['bytes'] and sha(d)==rec['sha256'];count+=1
 for c in rec['cuts']:
  x=b''.join(d.splitlines(keepends=True)[c['first_line']-1:c['last_line']]);assert x==Path(c['snapshot']).read_bytes() and len(x)==c['bytes'] and sha(x)==c['sha256'];count+=1
put('verification.json',{'status':'PASS','checked_at':now,'source_records':len(records),'cuts':sum(len(x['cuts']) for x in records),'byte_checks':count,'full_old_definitions_recovered_literal':True,'bundle_status':'OPEN'})
print(json.dumps({'status':'CLEAR / OPEN','report_sha256':sha((O/'report.txt').read_bytes()),'source_index_sha256':sha((O/'source-index.json').read_bytes()),'source_records':len(records),'cuts':sum(len(x['cuts']) for x in records),'byte_checks':count},indent=2))
