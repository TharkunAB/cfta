from pathlib import Path
import json,hashlib,datetime,difflib
repo=Path('/home/tritlo/Code/mcfta');out=Path('/tmp/mcfta-recursive-history-resources-20261027/invocation-admission-draft');sha=lambda b:hashlib.sha256(b).hexdigest();sources=[];cuts=[]
def add(name,spans=(),theorems=(),scope='used whole source contract and proof read'):
 p=repo/'lean/MicroCFTA'/(name+'.lean');raw=p.read_bytes();s=raw.decode();snapshot='inputs/lean/MicroCFTA/'+p.name;q=out/snapshot;q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(raw)
 sources.append(dict(path=str(p),source=str(p),snapshot=snapshot,bytes=len(raw),sha256=sha(raw),read_scope=scope))
 pairs=list(spans)
 for theorem in theorems:
  start=s.index('theorem '+theorem);end=s.index(' := by',start)+len(' := by');pairs.append((s[:start].count('\n')+1,s[:end].count('\n')+1))
 lines=raw.splitlines(keepends=True)
 for start,end in pairs:
  assert 1<=start<=end<=len(lines)
  b=b''.join(lines[start-1:end]);snapshot=f'cuts/{name}--{start}-{end}.lean';q=out/snapshot;q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(b)
  cuts.append(dict(path=str(p),source=str(p),snapshot=snapshot,start=start,end=end,source_sha256=sha(raw),bytes=len(b),sha256=sha(b)))
add('SourcePruningEnumerationCallbackAdmission',[(30,49)],['head_finite_complete_resources_with_callback_admission'])
add('SourcePruningEnumerationInvocationReceipts',theorems=['alternatives_finite_invocation_receipts'])
add('SourcePruningEnumerationHeadAdmission',[(41,66),(71,102)],scope='HeadAdmission/CompletedHeadReceipt read in full; original wrapper proof reused at prior checked identity')
add('SourcePruningEnumerationFiniteHeadResources',theorems=['head_finite_complete_resources'])
add('SourcePruningEnumerationFiniteReceiptResources',theorems=['receipt_finite_complete_resources'])
add('SourcePruningEnumerationFiniteSiblingResources',theorems=['alternatives_finite_complete_resources'])
add('SourcePruningEnumerationFiniteContract',[(29,50)])
add('SourcePruningEnumerationHookInvocation',[(41,70)],scope='actual Invocation constructors, whole output provenance proof and selected witness API read')
add('SourcePruningEnumerationFiniteReservation',[(60,67),(193,201),(233,243)],scope='actual step and reservation definitions/head-tail projections read; unrelated room proof suffix not freshly audited')
index=dict(version=1,status='OPEN DRAFT; ROOT CHECK PENDING',created=datetime.datetime.now().astimezone().isoformat(),sources=sources,cuts=cuts,read_scope='report.txt; focused direct APIs and actual induction, no broad import-closure audit',new_compiler_checks_executed=False)
(out/'source-pins.json').write_text(json.dumps(index,indent=2)+'\n')
old=(repo/'lean/MicroCFTA/SourcePruningEnumerationInvocationReceipts.lean').read_text();new=(out/'SourcePruningEnumerationInvocationAdmission.lean').read_text()
def contract(s,name):
 s=s[s.index('theorem '+name):];return s[:s.index(' := by')]
a=contract(old,'alternatives_finite_invocation_receipts');b=contract(new,'alternatives_finite_invocation_admissions');mapped=a.replace('theorem alternatives_finite_invocation_receipts','theorem alternatives_finite_invocation_admissions',1)
assert b.startswith(mapped) and b[len(mapped):].startswith(' ∧\n')
q=out/'contracts';q.mkdir(exist_ok=True)
(q/'old-entire-contract.txt').write_text(a);(q/'new-retained-old-contract.txt').write_text(b[:len(mapped)]);(q/'appended-admission.txt').write_text(b[len(mapped):]);(q/'new-entire-contract.txt').write_text(b)
(q/'comparison.json').write_text(json.dumps(dict(status='PASS',comparison='literal complete old contract prefix after only theorem-name substitution',original_bytes=len(a.encode()),original_sha256=sha(a.encode()),retained_bytes=len(mapped.encode()),retained_sha256=sha(mapped.encode()),exact_same_public_inputs_and_witness_order=True,grouping='The added conjunction is inside each original Invocation existential witness, after the old CompletedHeadReceipt. It is not a separate unrelated existential producer.',head_producer_call_count=new.count('head_finite_complete_resources_with_callback_admission'),same_recursive_Complete=True,new_runtime_definitions=0),indent=2)+'\n')
(out/'revisions/old-to-enriched.patch').write_text(''.join(difflib.unified_diff(old.splitlines(keepends=True),new.splitlines(keepends=True),fromfile='old/SourcePruningEnumerationInvocationReceipts.lean',tofile='new/SourcePruningEnumerationInvocationAdmission.lean')))
print(json.dumps(dict(sources=len(sources),cuts=len(cuts),cut_lines=sum(c['end']-c['start']+1 for c in cuts),old_contract_bytes=len(a.encode()),old_contract_sha256=sha(a.encode())),indent=2))
