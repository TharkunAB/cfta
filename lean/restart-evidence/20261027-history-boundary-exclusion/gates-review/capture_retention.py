from pathlib import Path
from datetime import datetime
from zoneinfo import ZoneInfo
import hashlib,json,shutil,re
A=Path('/tmp/mcfta-history-boundary-exclusion-20261027');O=A/'gates-review';R=Path('/home/tritlo/Code/mcfta')
def sha(d):return hashlib.sha256(d).hexdigest()
def save(rel,d):
 p=O/rel;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(d);return {'snapshot':str(p),'bytes':len(d),'sha256':sha(d)}
def put(rel,x):return save(rel,(json.dumps(x,indent=2,ensure_ascii=False)+'\n').encode())
h=O/'review-revisions/before-retention';h.mkdir(parents=True,exist_ok=True)
for n in ['source-index.json','report.txt','OPEN.json','verification.json']:
 if not (h/n).exists():shutil.copyfile(O/n,h/n)
records=json.loads((h/'source-index.json').read_text())['sources']
def capture(source,rel,spans,scope):
 p=Path(source);d=p.read_bytes();r={'source':str(p),**save(rel,d),'scope':'whole source/evidence identity','reviewed_scope':scope,'cuts':[]};records.append(r)
 for first,last,label in spans:
  assert 1<=first<=last<=len(d.splitlines(keepends=True))
  c=b''.join(d.splitlines(keepends=True)[first-1:last]);r['cuts'].append({'first_line':first,'last_line':last,**save(f'retention-cuts/{p.stem}-{first}-{last}.txt',c),'scope':'literal cut','purpose':label})
 return d
name='SourcePruningEnumerationDischargedRetention';expected='de72404ec21fe474e977bc6475b754e7e8fbc5c3a5d467e7d3d1f931adcf16aa'
source=capture(R/f'lean/MicroCFTA/{name}.lean',f'whole/{name}.lean',[(1,29,'module scope'),(31,64,'full actual head/callback/tail/discharge admission and exact retained gate'),(65,96,'actual own prefix/genuine children/complete trace'),(97,124,'all child cases and same-output opaque exclusion')],'whole installed126-line module read')
assert len(source.splitlines())==126 and sha(source)==expected
inputs=[
 ('SourcePruningEnumerationOpaqueOutputAttachment',[(30,84,'actual head/false callback/same tail own-output isolation and discharge exclusion')],'whole new consumer source already reviewed; focused declaration reread'),
 ('MergedOrdinaryHeight',[(88,98,'exact recursive boundary and closed ordinary operand cases')],'lines85-105 read; full identity retained'),
 ('SourcePruningEnumerationChildDispatch',[(156,166,'Empty gives actual [] rejection before any query')],'lines150-175 read; full identity retained'),
 ('SourcePruningEnumerationOpaqueEventTrace',[(44,79,'exact complete Trace split into actual singleton child occurrence'),(139,174,'actual captured completion child trace/finalizer')],'lines40-82 and139-174 read; full identity retained'),
 ('SourcePruningEnumerationSelectedReceiptLanguage',[(106,119,'full original retained and fresh-arity semantic gates')],'lines1-125 read; focused target comparison'),
 ('SourcePruningEnumerationEdgeInputs',[(25,75,'genuine actual own allocation and all closed child inputs')],'existing source derivation previously read; focused API reread')
]
for stem,spans,scope in inputs:capture(R/f'lean/MicroCFTA/{stem}.lean',f'retention-inputs/{stem}.lean',spans,scope)
checked=capture(A/f'strict-discharged-retention-1/MicroCFTA/{name}.lean',f'retention-strict/{name}.lean',[],'whole actual strict checked source matches installed')
report=capture(A/'strict-discharged-retention-1/report.json','retention-strict/report.json',[],'whole actual first strict report read')
raw=capture(A/'strict-discharged-retention-1/raw.log','retention-strict/raw.log',[],'whole actual empty strict output read')
r=json.loads(report);assert checked==source and r['source_sha256']==expected and r['exit_code']==0 and r['bytes']==len(raw)==0 and r['sha256']==sha(raw)
assert r['cgroup_limits']=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
header_start=source.index(b'theorem completed_head_output_retained\n');header_end=source.index(b' := by\n',header_start)
save('contracts/retention-full-header.txt',source[header_start:header_end])
conclusion=source[source.index('    ∀ tries residual,'.encode(),header_start):header_end]
old=(R/'lean/MicroCFTA/SourcePruningEnumerationSelectedReceiptLanguage.lean').read_bytes();begin=old.index(b'    (retained : ')+len(b'    (retained : ');end=old.index(b') :\n',begin);old_gate=old[begin:end]
# Cache-name substitution and whitespace only; all forall binders, implication, member and disjunction tokens remain exact.
normalize=lambda d:re.sub(rb'\s+',b' ',d.strip())
new_gate=conclusion.replace(b'before.core.counter',b'entered.core.counter')
assert normalize(new_gate)==normalize(old_gate)
save('contracts/retention-conclusion.txt',conclusion);save('contracts/old-selected-retained-gate.txt',old_gate)
assert source.count(b':= completed_head_opaque_output_not_discharged')==1
now=datetime.now(ZoneInfo('Europe/Stockholm')).isoformat()
review=f'''[{now}] CLEAR / OPEN: discharged same-output retention.

WHOLE SourcePruningEnumerationDischargedRetention read,126 lines / {expected}. Installed source is byte-identical to actual strict-discharged-retention-1 snapshot. First check passes exit0/raw0 with all linters/warnings fatal and actual memory.max/high4 GiB, swap0. This review ran no Lean/compiler/build/Git/network/board operation.

The exact conclusion is the complete existing retained gate: forall projected tries/residual and every actual generated child/bucket, ordinary node OR terminal bucket OR empty bucket. Its token sequence matches the old SelectedReceiptLanguage retained gate after only current-cache name and whitespace substitution; the comparison does not drop any quantifier, implication or disjunct. This new helper is a local observer, not an old completion producer replacement.

Admission remains actual CompletedHeadReceipt, the exact false callback singleton, SAME returned inventory/caller/FULL Memos/recorded metadata/framed callback cache/literal restart decision ResourceHistory, and Discharged at that SAME output.cache. No Canonical, fresh arity, Satisfies, desired retained predicate, or separate future success is assumed. Discharged is the explicit structural eligibility premise already needed by rendering, not desired semantic acceptance.

All cases are covered. EdgeInputs.complete derives genuine available closed child inputs from the actual stored parent and selected edge. captured_complete_trace uses the original head's actual stable bound to expose the same complete ordered trace. For each child occurrence, a terminal bucket satisfies the second disjunct directly. A nonterminal Mu/Union boundary invokes the actual own-output opaque theorem once and contradicts the supplied SAME-output Discharged. A closed non-boundary is Empty or an ordinary node by ordinary_operand; its closed premise excludes a free reference. Empty cannot occur in that complete Trace: split_event exposes an actual successful singleton row, while ChildDispatch.empty is exactly [] rejection. Every remaining ordinary node satisfies the first disjunct. Empty buckets remain explicitly permitted by the target predicate; no case is narrowed away.

No source blocker found. The proof derives child retention only along the head/false callback/actual admitted tail of the discharged output. It does not claim all outputs are discharged, all siblings share a cache, semantic acceptance/coverage, or physical Haskell correctness. Checked fresh arity is a separate source-provenance result. Existing old semantic conclusions still need a concrete integration wrapper, whose whole old contract recovery remains pending.

Earlier checked-arity source review stays CLEAR. Both phase reports, complete theorem/target-gate text, exact input identities and focused literal cuts are preserved. Keep this bundle OPEN until the final consumer, installed-source/build/public/Audit and document claim receipts are reviewed.
'''
save('retention-review.txt',review.encode())
save('report.txt',(h/'report.txt').read_bytes()+b'\n'+review.encode())
put('retention-check.json',{'status':'CLEAR','reviewed_at':now,'source_sha256':expected,'line_count':126,'strict_exit_code':0,'strict_raw_bytes':0,'actual_memory_max':4294967296,'swap_max':0,'target_gate_token_comparison_exact_after_cache_rename_and_whitespace':True,'gate_mapping':'before.core.counter → entered.core.counter; whitespace only','all_value_cases_covered':True,'canonical_or_fresh_arity_or_satisfies_premise':False,'same_actual_head_callback_tail_own_output':True})
put('source-index.json',{'schema':'whole sources and explicit literal cuts','cut_convention':'one-based inclusive lines; splitlines(keepends=True); original LF retained','sources':records})
put('OPEN.json',{'status':'OPEN','reviewed_at':now,'current_review':'CLEAR checked arity and discharged retention','reason':'Await exact selected consumer and final source/build/public/Audit/document claims.','publication_outcome':'not asserted'})
checks=0
for rec in records:
 d=Path(rec['source']).read_bytes();assert d==Path(rec['snapshot']).read_bytes() and len(d)==rec['bytes'] and sha(d)==rec['sha256'];checks+=1
 for c in rec['cuts']:
  x=b''.join(d.splitlines(keepends=True)[c['first_line']-1:c['last_line']]);assert x==Path(c['snapshot']).read_bytes() and len(x)==c['bytes'] and sha(x)==c['sha256'];checks+=1
put('verification.json',{'status':'PASS','checked_at':now,'source_records':len(records),'cuts':sum(len(x['cuts']) for x in records),'byte_checks':checks,'bundle_status':'OPEN'})
print(json.dumps({'status':'CLEAR / OPEN','report_sha256':sha((O/'report.txt').read_bytes()),'source_index_sha256':sha((O/'source-index.json').read_bytes()),'source_records':len(records),'cuts':sum(len(x['cuts']) for x in records),'byte_checks':checks},indent=2))
