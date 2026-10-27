from pathlib import Path
import json, hashlib, datetime, shutil
repo=Path('/home/tritlo/Code/mcfta');area=Path('/tmp/mcfta-recursive-admission-20261027');out=area/'ordinary-receipts-draft'
sha=lambda b:hashlib.sha256(b).hexdigest()
consumer=out/'consumer-review';consumer.mkdir(exist_ok=True)
for name in ['source-pins.json','report.txt','review-status.json']:
 q=consumer/('before-'+name)
 if not q.exists():q.write_bytes((out/name).read_bytes())
idx=json.loads((out/'source-pins.json').read_text())
def add(name, declarations):
 p=repo/'lean/MicroCFTA'/(name+'.lean');raw=p.read_bytes();s=raw.decode();snapshot='inputs/lean/MicroCFTA/'+name+'.lean'
 q=out/snapshot;q.parent.mkdir(exist_ok=True,parents=True);q.write_bytes(raw)
 assert not any(x['source']==str(p) for x in idx['sources'])
 idx['sources'].append(dict(path=str(p),source=str(p),snapshot=snapshot,bytes=len(raw),sha256=sha(raw),read_scope='whole actual consumer/helper module source reviewed; exact final source identity'))
 lines=raw.splitlines(keepends=True)
 for declaration in declarations:
  startpos=s.index('theorem '+declaration);endpos=s.index(' := by',startpos)+len(' := by')
  start=s[:startpos].count('\n')+1;end=s[:endpos].count('\n')+1
  b=b''.join(lines[start-1:end]);cut=f'cuts/{name}--{start}-{end}.lean';(out/cut).write_bytes(b)
  idx['cuts'].append(dict(path=str(p),source=str(p),snapshot=cut,start=start,end=end,source_sha256=sha(raw),bytes=len(b),sha256=sha(b)))
add('SourcePruningEnumerationOrdinaryReceiptLanguage',['CompletedHeadReceipt.sound_ordinary_input','CompletedHeadReceipt.sound_ordinary_callback_input'])
add('SourcePruningEnumerationOrdinaryInvocationLanguage',['ordinary_finite_complete_invocation_semantics'])
add('SourcePruningEnumerationInvocationLanguage',['CompletedHeadReceipt.sound_scan_input'])
add('SourcePruningEnumerationObservedFramesLanguage',['enter_semantics','recordTypes_success_semantics'])
add('SourcePruningEnumerationEntryCanonical',['enter_canonical'])
evidence=[]
for name,module in [('strict-ordinary-language-1','SourcePruningEnumerationOrdinaryReceiptLanguage'),('strict-ordinary-language-2','SourcePruningEnumerationOrdinaryReceiptLanguage'),('strict-ordinary-language-3','SourcePruningEnumerationOrdinaryReceiptLanguage'),('strict-ordinary-producer-language-1','SourcePruningEnumerationOrdinaryInvocationLanguage'),('strict-ordinary-producer-language-2','SourcePruningEnumerationOrdinaryInvocationLanguage')]:
 original=area/name;dest=out/'evidence'/name;(dest/'MicroCFTA').mkdir(parents=True,exist_ok=True)
 for rel in ['report.json','raw.log','MicroCFTA/'+module+'.lean']:
  b=(original/rel).read_bytes();(dest/rel).write_bytes(b)
  evidence.append(dict(source=str(original/rel),snapshot=str((dest/rel).relative_to(out)),bytes=len(b),sha256=sha(b)))
 r=json.loads((dest/'report.json').read_text());assert sha((dest/'MicroCFTA'/(module+'.lean')).read_bytes())==r['source_sha256']
 if name.endswith('-3') or name=='strict-ordinary-producer-language-2':
  assert r['exit_code']==0 and (dest/'raw.log').read_bytes()==b''
  assert (repo/'lean/MicroCFTA'/(module+'.lean')).read_bytes()==(dest/'MicroCFTA'/(module+'.lean')).read_bytes()
idx['evidence']=evidence
p=repo/'lean/MicroCFTA'
def header(name,theorem):
 s=(p/(name+'.lean')).read_text();s=s[s.index('theorem '+theorem):];return s[:s.index(' := by')]
a=header('SourcePruningEnumerationOrdinaryInvocationResources','ordinary_finite_complete_invocation_resources')
b=header('SourcePruningEnumerationOrdinaryInvocationLanguage','ordinary_finite_complete_invocation_semantics')
mapped=a.replace('theorem ordinary_finite_complete_invocation_resources','theorem ordinary_finite_complete_invocation_semantics',1)
assert b.startswith(mapped) and b[len(mapped):].startswith(' ∧\n')
(consumer/'old-full-producer-contract.txt').write_text(a)
(consumer/'retained-producer-contract.txt').write_text(b[:len(mapped)])
(consumer/'appended-semantic-clause.txt').write_text(b[len(mapped):])
proof=(p/'SourcePruningEnumerationOrdinaryInvocationLanguage.lean').read_text().split(' := by',1)[1]
assert proof.count('ordinary_finite_complete_invocation_resources ')==1
comparison=dict(status='PASS',comparison='literal complete prior admission and output, after declaration-name substitution only',prior_bytes=len(a.encode()),prior_sha256=sha(a.encode()),retained_bytes=len(mapped.encode()),retained_sha256=sha(mapped.encode()),one_original_producer_call=True,semantic_gates_appended_after_original_unconditional_resource_packet=True)
(consumer/'comparison.json').write_text(json.dumps(comparison,indent=2)+'\n')
review='''CONSUMER SOURCE REVIEW CLEAR; SEAL REMAINS HELD\n\nThe final OrdinaryReceiptLanguage source a8edd0b40396aeebe92c91cae2f9c04529ddad99bda42e19a259f091aa143335 matches Root's strict-ordinary-language-3 source/report and literal empty log. Its earlier strict1 namespace failure and strict2 intermediate successful source are retained. Both current theorems were read in full. The original entry receipt derives entered Canonical with enter_canonical. sound_scan_input uses the actual aggregate Post and the receipt's full input/output memos, so satisfaction is restored at the scan's original native heap. enter_semantics then restores the original pre-entry core at that same original native heap. No full memo equality follows from the query projection. The false-callback corollary consumes an actual successful false callback at the completed core; recordTypes_success_semantics supplies only its actual fixed-heap frame equivalence. It assumes no recursive callback correctness.\n\nThe final OrdinaryInvocationLanguage source 78a2197b2e65178c3e5f4a616df5cec277b7be0cf15488cea2dc7f62f3f25c04 matches Root's strict-ordinary-producer-language-2 source/report and literal empty log. Its first unknown Suspended namespace failure is retained. The whole previous finite-closed ordinary producer declaration, including admission and every original output, is a literal prefix after declaration-name substitution. The theorem calls that producer once. It retains the same rich actual invocation witness and same completed receipt. Its semantic append keeps initial Canonical, actual fresh-arity and child-retention conditions explicit and local to the selected actual edge. Counter equality transports only the start index in those conditions. The actual entry equation at the common sufficient work fuel gives Success at the retained entered cache; no second entry producer is called. Stored-slot equality identifies the head's handle. lookupNode_keeps from the actual prefix Post identifies the actual head parent with the original decoded parent. This yields backward satisfaction, actual selected-edge/parent meaning, inherited Holds and the fragment fill equation at the actual completed head.\n\nThe append is conditional on satisfaction at that completed head. It does not derive the satisfaction premise, semantic gates, whole recursive acceptance or coverage. The false-callback law is separate from correctness of any later subtree. Initial Canonical remains an explicit conditional semantic gate, rather than a new unconditional resource admission premise. No rejection safety, full memos equality, unbounded convergence, Haskell certification or stronger H6 claim follows. No runtime definition changes in these modules. This is source review against Root's already executed checks; this review executes no compiler or build.\n\nRead scope: whole final new consumers and the directly used sound_scan_input, enter_semantics, recordTypes_success_semantics and enter_canonical modules. Imported theorem dependencies remain their checked API contracts; this is not a new import-closure audit. The bundle is deliberately open until Root gives the final seal cue.\n'''
(consumer/'report.txt').write_text(review)
(out/'report.txt').write_text((consumer/'before-report.txt').read_text()+'\n--- Final actual semantic consumer review ---\n\n'+review)
idx['observed_at']=datetime.datetime.now().astimezone().isoformat();idx['status']='OPEN CLEAR PRODUCER AND CONSUMER SOURCE REVIEW; SEAL HELD BY ROOT'
(out/'source-pins.json').write_text(json.dumps(idx,indent=2)+'\n')
status=json.loads((out/'review-status.json').read_text());status.update(status='PRODUCER AND CONSUMER SOURCE REVIEW CLEAR; OPEN, NOT SEALED',consumer_source_review='consumer-review/report.txt',reason='Root requested hold pending final seal cue; actual final consumer checked source identities now included.')
(out/'review-status.json').write_text(json.dumps(status,indent=2)+'\n')
print(json.dumps({'sources':len(idx['sources']),'cuts':len(idx['cuts']),'cut_lines':sum(c['end']-c['start']+1 for c in idx['cuts']),'additional_evidence_files':len(evidence),'consumer_prior_contract_bytes':comparison['prior_bytes'],'consumer_review':'CLEAR','sealed':False},indent=2))
