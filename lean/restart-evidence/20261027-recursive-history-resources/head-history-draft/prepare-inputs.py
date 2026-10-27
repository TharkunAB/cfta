from pathlib import Path
import json,hashlib,datetime
repo=Path('/home/tritlo/Code/mcfta');out=Path('/tmp/mcfta-recursive-history-resources-20261027/head-history-draft');sha=lambda b:hashlib.sha256(b).hexdigest();sources=[];cuts=[]
def add(name,spans=(),theorems=(),scope='whole used contract and proof source read'):
 p=repo/'lean/MicroCFTA'/(name+'.lean');raw=p.read_bytes();s=raw.decode();snapshot='inputs/lean/MicroCFTA/'+p.name;q=out/snapshot;q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(raw)
 sources.append(dict(path=str(p),source=str(p),snapshot=snapshot,bytes=len(raw),sha256=sha(raw),read_scope=scope))
 pairs=list(spans)
 for theorem in theorems:
  start=s.index('theorem '+theorem);end=s.index(' := by',start)+len(' := by');pairs.append((s[:start].count('\n')+1,s[:end].count('\n')+1))
 for start,end in pairs:
  b=b''.join(raw.splitlines(keepends=True)[start-1:end]);snapshot=f'cuts/{name}--{start}-{end}.lean';q=out/snapshot;q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(b)
  cuts.append(dict(path=str(p),source=str(p),snapshot=snapshot,start=start,end=end,source_sha256=sha(raw),bytes=len(b),sha256=sha(b)))
add('SourcePruningEnumerationCallbackAdmission',[(30,46)],['head_finite_complete_resources_with_callback_admission'])
add('SourcePruningEnumerationFiniteCallbackHistory',theorems=['callback_finite_complete_resources_with_history'])
add('SourcePruningEnumerationFiniteHistoryContract',theorems=['CompleteWithHistory.forget'],scope='whole concrete V2 schema, ResourceHistory/CompleteWithHistory and forget/base proof read; Root zero-rewrite correction retained at current identity')
add('SourcePruningEnumerationHeadAdmission',[(71,102)],scope='CompletedHeadReceipt fields and actual head wrapper read; prior unchanged wrapper proof is checked context')
add('SourcePruningEnumerationFiniteContract',[(28,48)])
add('SourcePruningEnumerationFiniteReservation',[(64,69),(192,199)],scope='actual paired seed and reservation definitions read; unrelated numeric-room suffix not freshly audited')
index=dict(version=1,status='OPEN DRAFT; ROOT STRICT CHECK PENDING',created=datetime.datetime.now().astimezone().isoformat(),sources=sources,cuts=cuts,new_compiler_checks_executed=False,read_scope='report.txt; direct contracts and actual common-bound proof, not import closure')
(out/'source-pins.json').write_text(json.dumps(index,indent=2)+'\n')
old=(repo/'lean/MicroCFTA/SourcePruningEnumerationCallbackAdmission.lean').read_text();new=(out/'SourcePruningEnumerationFiniteHeadHistory.lean').read_text()
def header(s,name):
 s=s[s.index('theorem '+name):];return s[:s.index(' := by')]
a=header(old,'head_finite_complete_resources_with_callback_admission');b=header(new,'head_finite_complete_resources_with_history');append=(out/'supported-history-appendix.txt').read_text()
restored=b.replace(append,'          | .stopped _ _ _ => True) ∧',1).replace('          (match outcome with','          match outcome with',1).replace('head_finite_complete_resources_with_history','head_finite_complete_resources_with_callback_admission',1).replace('(recursive : CompleteWithHistory (bits := bits)','(recursive : Complete (bits := bits)',1)
assert restored==a
folder=out/'contracts';folder.mkdir(exist_ok=True)
for name,text in [('old-entire-contract.txt',a),('new-entire-contract.txt',b),('restored-entire-old-contract.txt',restored)]: (folder/name).write_text(text)
(folder/'comparison.json').write_text(json.dumps(dict(status='PASS',original_bytes=len(a.encode()),original_sha256=sha(a.encode()),entire_old_contract_preserved=True,transformations=['Remove only supported same-outcome receipt-history appendix and its added match parentheses','Reverse theorem name','Forget stronger smaller-depth CompleteWithHistory to original Complete'],same_original_head_producer_once=True,new_callback_history_producer_once=True,new_producer_premises='Only explicit stronger smaller-depth induction hypothesis; no new current/future success or semantic premise',new_runtime_definitions=0),indent=2)+'\n')
print(json.dumps(dict(sources=len(sources),cuts=len(cuts),cut_lines=sum(c['end']-c['start']+1 for c in cuts),original_contract_bytes=len(a.encode()),original_contract_sha256=sha(a.encode())),indent=2))
