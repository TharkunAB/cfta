from pathlib import Path
from datetime import datetime
from zoneinfo import ZoneInfo
import hashlib,json,shutil,re
A=Path('/tmp/mcfta-history-boundary-exclusion-20261027');O=A/'gates-review';R=Path('/home/tritlo/Code/mcfta')
def sha(d):return hashlib.sha256(d).hexdigest()
def save(rel,d):
 p=O/rel;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(d);return {'snapshot':str(p),'bytes':len(d),'sha256':sha(d)}
def put(rel,x):return save(rel,(json.dumps(x,indent=2,ensure_ascii=False)+'\n').encode())
h=O/'review-revisions/before-finite';h.mkdir(parents=True,exist_ok=True)
for n in ['source-index.json','report.txt','OPEN.json','verification.json']:
 if not (h/n).exists():shutil.copyfile(O/n,h/n)
records=json.loads((h/'source-index.json').read_text())['sources']
def capture(source,rel,spans,scope):
 p=Path(source);d=p.read_bytes();r={'source':str(p),**save(rel,d),'scope':'whole source/evidence identity','reviewed_scope':scope,'cuts':[]};records.append(r)
 for first,last,label in spans:
  assert 1<=first<=last<=len(d.splitlines(keepends=True)),(p,last);c=b''.join(d.splitlines(keepends=True)[first-1:last]);r['cuts'].append({'first_line':first,'last_line':last,**save(f'finite-cuts/{p.stem}-{first}-{last}.txt',c),'scope':'literal cut','purpose':label})
 return d
name='SourcePruningEnumerationFiniteHistoryRendering';expected='849f031469d89cbaa6fc49a5497d75dcfcdc57bcb93188dda73c3a145aca4e7b'
new=capture(R/f'lean/MicroCFTA/{name}.lean',f'final-sources/{name}.lean',[(1,29,'module context'),(31,57,'old initial inputs and full result packet retained'),(58,88,'observer certificate/render/discharge/lookup antecedents and constructed result'),(89,98,'old producer once then same output observer')],'whole100-line installed final source read')
old=capture(R/'lean/MicroCFTA/SourcePruningEnumerationFiniteHistoryCanonical.lean','finite-inputs/SourcePruningEnumerationFiniteHistoryCanonical.lean',[(27,61,'whole original canonical producer contract and body')],'whole original63-line source read')
assert sha(new)==expected and len(new.splitlines())==100
checks=[];first=None
for check in ['strict-finite-history-rendering-1','strict-finite-history-rendering-final-1']:
 checked=capture(A/check/f'MicroCFTA/{name}.lean',f'finite-strict/{check}/{name}.lean',[],'whole actual strict source retained; both historical and final variants passed')
 report=capture(A/check/'report.json',f'finite-strict/{check}/report.json',[],'whole actual strict report read')
 raw=capture(A/check/'raw.log',f'finite-strict/{check}/raw.log',[],'whole empty actual strict output read')
 r=json.loads(report);assert sha(checked)==r['source_sha256'] and r['exit_code']==0 and r['bytes']==len(raw)==0 and r['sha256']==sha(raw)
 assert r['cgroup_limits']=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
 if check.endswith('final-1'):assert checked==new
 else:first=checked
 checks.append({'check':check,'source_sha256':sha(checked),'exit_code':0,'raw_bytes':0})
strip_comment=lambda d:re.sub(rb'/-!\n.*?\n-/\n',b'',d,count=1,flags=re.S)
assert strip_comment(first)==strip_comment(new)

def header(data,name):
 start=data.index(('theorem '+name+'\n').encode());end=data.index(b' := by\n',start);return data[start:end]
oh=header(old,'run_finite_complete_resources_canonical');nh=header(new,'run_finite_complete_resources_render_sound')
kept,observer=nh.rsplit(' ∧\n      ∀ extra output, output ∈'.encode(),1)
assert kept.endswith(b'Canonical output.cache.core)')
recovered=kept[:-1].replace(b'theorem run_finite_complete_resources_render_sound\n',b'theorem run_finite_complete_resources_canonical\n',1).replace('      (∀ output ∈'.encode(),'      ∀ output ∈'.encode(),1)
assert oh==recovered and len(oh)==2235
for tag,d in [('old-full-header',oh),('new-full-header',nh),('recovered-old-full-header',recovered),('new-observer','      ∀ extra output, output ∈'.encode()+observer)]:save(f'finite-contracts/{tag}.txt',d)
assert new.count(b'    run_finite_complete_resources_canonical holeKey')==1
put('finite-contract-comparison.json',{'status':'PASS','old_full_header_bytes':len(oh),'old_full_header_sha256':sha(oh),'recovered_full_header_sha256':sha(recovered),'literal_whole_old_header':True,'all_original_initial_inputs_unchanged':True,'old_producer_calls':1,'mapping':['Remove only appended observer conjunction.','Remove grouping parentheses around original outputCanonical family.','Restore original theorem name.'],'new_certificate_position':'Observer antecedent after original existential bound/outcome and ENTIRE old result packet, at same bound+extra and output.','finite_first_and_final_checks_both_passed':True,'first_to_final_only_module_documentation':True,'strict_checks':checks})
# Recheck all actual installed final sources against their successful authoritative snapshots.
modules=json.loads((A/'modules.json').read_text());strict=json.loads((A/'strict-checks.json').read_text());installed=[]
for module in modules:
 d=capture(R/f'lean/MicroCFTA/{module}.lean',f'installed/{module}.lean',[],'installed final identity compared with successfully checked source and previously read whole source')
 check=A/strict[module];r=json.loads((check/'report.json').read_text());checked=(check/f'MicroCFTA/{module}.lean').read_bytes();assert d==checked and sha(d)==r['source_sha256'] and r['exit_code']==0
 installed.append({'module':module,'bytes':len(d),'lines':len(d.splitlines()),'sha256':sha(d),'strict_check':strict[module]})
assert len(installed)==7 and sum(x['lines'] for x in installed)==892
for rel in ['modules.json','strict-checks.json','public-declarations.json','public-definitions.json']:
 capture(A/rel,'checkpoint-inputs/'+rel,[],'whole final module/check/public declaration lists read; public output/Audit/docs pending')
put('installed-seven.json',{'status':'PASS','modules':installed,'lines':sum(x['lines'] for x in installed),'new_public_theorems':10,'new_data_definitions':2})
now=datetime.now(ZoneInfo('Europe/Stockholm')).isoformat()
review=f'''[{now}] CLEAR / OPEN: finite producer with conditional actual rendered-output observer.

WHOLE installed FiniteHistoryRendering100 lines / {expected} read. Its final strict check passes0/raw0 under actual memory.max/high4 GiB,swap0,all linters/warnings fatal. The earlier strict-finite-history-rendering-1 ALSO passes0/raw0; it differs from final only in module documentation. Both exact source/report/log variants are retained without inventing a failure. All seven installed final modules match their authoritative successful strict snapshots and previously reviewed complete sources:892 total source lines,ten new public theorems andtwo printed data declarations planned.

The ENTIRE2,235-byte original FiniteHistoryCanonical producer header recovers LITERALLY / {sha(oh)}. Mapping removes only the appended observer, removes the grouping parentheses around the original Canonical-output family, and restores the old theorem name. Every original initial admission stays unchanged, including Packet, native Fits/guard carrier, selector membership/length, mass ceiling, finite reservation and initial Canonical. The old producer is called ONCE. Its same existential bound/outcome and complete stable runtime, OutcomeResources, per-output ResourceHistory and Canonical family are forwarded unchanged.

The appended observer is after that ENTIRE old packet. It quantifies extra/output and actual membership, then requires the additional ResourceHistoryWithArity at exactly SAME bound+extra, original runtime inputs/fullMemos/cache/seed/ceiling/literal restart decision and SAME output. It then takes actual own-output render Success, discharge, residual checks and ORIGINAL stored-root/lookup receipts. No arity decoration, desired final assignment/acceptance, later success or extra resource forecast is added to original producer admission. No bound moves inside an output or certificate quantifier. The observer invokes the already checked history render theorem once to construct assignment/original native acceptance/all suspended Holds/actual rendering Frame and own-output Satisfies.

Latest whole-history/source claims remain scoped correctly. The decorated-history forget maps retain complete original actual histories. Initial Canonical plus actual operations supplies later Canonical. Actual parked and opaque events are excluded only by SAME own-output discharge. The lower prefix/ordinary callback laws preserve actual post-prefix ordinaryInventory/full ordinaryMemos and actual same captured cache, without rebasing inventory. Original assignment is constructed from actual own rendering, not assumed. Native output_packet comes directly from the final actual history tag rather than a supplied final Packet/Safe premise.

No source blocker found. Global creation of numeric own-arity decorations from all actual checked construction/intersection origins is STILL OPEN. The old finite producer guarantees unannotated actual histories; this wrapper adds a conditional observer, not automatic bare-producer all-output original acceptance. Coverage and physical Haskell correspondence remain open. All old H6/captured public signatures still require final byte comparison when public readback arrives. Keep this review OPEN for actual aggregate/Audit/public and final document claim receipts. Previous frozen areas are untouched.
'''
save('finite-review.txt',review.encode());save('report.txt',(h/'report.txt').read_bytes()+b'\n'+review.encode())
put('source-index.json',{'schema':'whole sources and explicit literal cuts','cut_convention':'one-based inclusive lines; splitlines(keepends=True); original LF retained','sources':records})
put('OPEN.json',{'status':'OPEN','reviewed_at':now,'current_review':'CLEAR all seven final installed sources and exact finite conditional observer','reason':'Await final source/public/Audit/document claims.','publication_outcome':'not asserted'})
count=0
for rec in records:
 d=Path(rec['source']).read_bytes();assert d==Path(rec['snapshot']).read_bytes() and len(d)==rec['bytes'] and sha(d)==rec['sha256'];count+=1
 for c in rec['cuts']:
  x=b''.join(d.splitlines(keepends=True)[c['first_line']-1:c['last_line']]);assert x==Path(c['snapshot']).read_bytes() and len(x)==c['bytes'] and sha(x)==c['sha256'];count+=1
put('verification.json',{'status':'PASS','checked_at':now,'source_records':len(records),'cuts':sum(len(x['cuts']) for x in records),'byte_checks':count,'full_old_finite_header_literal':True,'seven_installed_match_strict':True,'bundle_status':'OPEN'})
print(json.dumps({'status':'CLEAR / OPEN','report_sha256':sha((O/'report.txt').read_bytes()),'source_index_sha256':sha((O/'source-index.json').read_bytes()),'source_records':len(records),'cuts':sum(len(x['cuts']) for x in records),'byte_checks':count},indent=2))
