from pathlib import Path
import json,hashlib,datetime
repo=Path('/home/tritlo/Code/mcfta');area=Path('/tmp/mcfta-recursive-history-resources-20261027');out=area/'invocation-admission-draft';sha=lambda b:hashlib.sha256(b).hexdigest();assert not (out/'FROZEN.json').exists()
idx=json.loads((out/'source-pins.json').read_text());(out/'revisions/pre-final-source-index.json').write_bytes((out/'source-pins.json').read_bytes())
# Retain initial literal cuts. The final cuts contain complete declarations.
corrections={('SourcePruningEnumerationCallbackAdmission',30,49):(30,46),('SourcePruningEnumerationFiniteContract',29,50):(28,48),('SourcePruningEnumerationHookInvocation',41,70):(38,68),('SourcePruningEnumerationFiniteReservation',60,67):(64,69),('SourcePruningEnumerationFiniteReservation',193,201):(192,199),('SourcePruningEnumerationFiniteReservation',233,243):(235,244)}
for c in idx['cuts']:
 name=Path(c['source']).stem;key=(name,c['start'],c['end'])
 if key not in corrections:continue
 old=out/c['snapshot'];saved=out/'revisions/initial-cuts'/old.name;saved.parent.mkdir(parents=True,exist_ok=True);old.rename(saved)
 start,end=corrections[key];raw=Path(c['source']).read_bytes();b=b''.join(raw.splitlines(keepends=True)[start-1:end]);snapshot=f'cuts/{name}--{start}-{end}.lean';(out/snapshot).write_bytes(b);c.update(snapshot=snapshot,start=start,end=end,bytes=len(b),sha256=sha(b))
expected=[('strict-invocation-admission-1','SourcePruningEnumerationInvocationAdmission','cec61090ba1f5031c6a2a676ab0092487772803b7f6f1fc7c3f8d33d2cbc868e'),('strict-sibling-invocation-admission-1','SourcePruningEnumerationSiblingInvocationAdmission','65777bb213e2c0a9d7d0a374671c97fc5485759e2e2ad4a78b0df397df6a00ea'),('strict-ordinary-invocation-admission-1','SourcePruningEnumerationOrdinaryInvocationAdmission','097038ea24988e11dede6d9e147d06db79a3885820e83621b4d3c03ab19250d5')]
checks=[]
for name,module,digest in expected:
 p=repo/'lean/MicroCFTA'/(module+'.lean');raw=p.read_bytes();assert sha(raw)==digest
 checked=out/'checked-source'/p.name;checked.parent.mkdir(exist_ok=True);checked.write_bytes(raw)
 dest=out/'evidence'/name;(dest/'MicroCFTA').mkdir(parents=True,exist_ok=True)
 for rel in ['report.json','raw.log','MicroCFTA/'+p.name]:
  source=area/name/rel;b=source.read_bytes();q=dest/rel;q.write_bytes(b);idx.setdefault('evidence',[]).append(dict(source=str(source),snapshot=str(q.relative_to(out)),bytes=len(b),sha256=sha(b)))
 r=json.loads((dest/'report.json').read_text());assert r['source_sha256']==digest and r['exit_code']==0 and (dest/'raw.log').read_bytes()==b'' and (dest/'MicroCFTA'/p.name).read_bytes()==raw
 checks.append(dict(module=module,source_sha256=digest,strict=name,exit_code=0,raw_bytes=0))
 if module=='SourcePruningEnumerationInvocationAdmission':
  assert (out/'revisions/001-initial.lean').read_bytes()==raw
  snapshot='inputs/lean/MicroCFTA/'+p.name;(out/snapshot).write_bytes(raw);idx['sources'].append(dict(path=str(p),source=str(p),snapshot=snapshot,bytes=len(raw),sha256=digest,read_scope='whole final new helper read; initial draft and installed strict1 input byte-identical'))
  text=raw.decode();startpos=text.index('theorem alternatives_finite_invocation_admissions');endpos=text.index(' := by',startpos)+len(' := by');start=text[:startpos].count('\n')+1;end=text[:endpos].count('\n')+1;b=b''.join(raw.splitlines(keepends=True)[start-1:end]);snapshot=f'cuts/{module}--{start}-{end}.lean';(out/snapshot).write_bytes(b);idx['cuts'].append(dict(path=str(p),source=str(p),snapshot=snapshot,start=start,end=end,source_sha256=digest,bytes=len(b),sha256=sha(b)))
(out/'checked-source/checks.json').write_text(json.dumps(checks,indent=2)+'\n')
report=(out/'report.txt').read_text();(out/'revisions/initial-report.txt').write_text(report)
report=report.replace('SOURCE-CONNECTED INITIAL DRAFT COMPLETE; OPEN FOR ROOT COMPILER RECEIPTS','FINAL SOURCE CLAIM REVIEW CLEAR').replace('The bundle must remain unsealed until Root supplies the actual checked snapshots.','Root has supplied all three passing strict snapshots. The bundle now binds and seals their exact checked inputs.')
family='''\nROOT SIBLING AND ORDINARY ADMISSION LIFTS: CLEAR\n\nThe new SiblingInvocationAdmission and OrdinaryInvocationAdmission sources were read against their exact original resource wrappers. Independent comparison retains the old and new full declarations/contracts and proves that all four public declaration/proof bodies are identical after precisely removing the appended RecursiveCallbackAdmission, reversing the public/helper names, and normalizing only whitespace/comments. It drops no old predicate, binder or proof body. Root's independent root-family-comparison.json is preserved alongside this comparison. The extra admission stays inside each old actual invocation's same existential witnesses, after its CompletedHeadReceipt.\n\nThe sibling wrapper calls the original complete scan once and the enriched invocation helper once. The common bound is scanBound+receiptBound; both old scan and rich callback families use that exact work fuel, including the resume continuation closure. The ordinary wrapper calls the original ordinary producer once, retaining its same entered core, exact entry row, counter/values/index equalities, Packet and all native/resource/receipt/output/stopped/finished fields. Its existing Ready/IncomingAvoid/mass/frame proof admits the enriched helper at that same entered cache. The actual OrdinaryInvocation entry row is inverted at the same combined bound. It does not introduce a second entry producer or silently compare arbitrary partial fuels.\n\nBoth lifts retain the actual head input full memos and original-to-head aggregate Post. The appended admission uses returnedInventory, reached Caller, returnedMemos and completed after cache from the same old receipt. Its seed is exactly afterHead headSeed inherited and its mass ceiling is exactly massCeil headSeed capturedMass inherited. The caller/query/captured-cache distinction and actual post-hook suffix endpoint are unchanged. The finite corollaries remove only the abstract Complete input by supplying the existing proven finite_complete. There is no new future progress, semantic assignment, Canonical, arity, retention or IsolatedPending premise, and no new derivation of those semantic gates. Rejected/stopped caches acquire no new safety claim.\n\nAll three new modules pass Root's first strict check with warnings as errors/all linters and literal empty raw logs. The helper is byte-identical to initial draft001 cec61090ba1f5031c6a2a676ab0092487772803b7f6f1fc7c3f8d33d2cbc868e. The sibling lift is 65777bb213e2c0a9d7d0a374671c97fc5485759e2e2ad4a78b0df397df6a00ea. The ordinary lift is 097038ea24988e11dede6d9e147d06db79a3885820e83621b4d3c03ab19250d5. Exact reports, empty logs and checked source copies are retained. No new check was run by this review. Whole sources and literal focused cuts preserve exact identities, including prior cut revisions. This package proves resource admission of actual callbacks. It does not prove a stronger history-aware Complete contract, whole recursive backward acceptance, coverage or physical Haskell correspondence. Future history composition remains separate.\n'''
report+=family;(out/'report.txt').write_text(report);(out/'root-family-review/report.txt').write_text(family.lstrip())
idx['status']='FINAL SOURCE CLAIM REVIEW CLEAR; FROZEN';idx['new_compiler_checks_executed']=False;(out/'source-pins.json').write_text(json.dumps(idx,indent=2)+'\n')
for s in idx['sources']:
 b=Path(s['source']).read_bytes();assert b==(out/s['snapshot']).read_bytes() and sha(b)==s['sha256']
for c in idx['cuts']:
 b=b''.join(Path(c['source']).read_bytes().splitlines(keepends=True)[c['start']-1:c['end']]);assert b==(out/c['snapshot']).read_bytes() and sha(b)==c['sha256']
for e in idx.get('evidence',[]):
 b=Path(e['source']).read_bytes();assert b==(out/e['snapshot']).read_bytes() and sha(b)==e['sha256']
now=datetime.datetime.now().astimezone().isoformat();files={}
for p in sorted(out.rglob('*')):
 if p.is_file() and p not in [out/'pins.json',out/'FROZEN.json']:
  b=p.read_bytes();files[str(p.relative_to(out))]=dict(bytes=len(b),sha256=sha(b))
b=(json.dumps(dict(created=now,files=files),indent=2)+'\n').encode();(out/'pins.json').write_bytes(b)
frozen=dict(created=now,status='FROZEN / CLEAR',payload_count=len(files),exact_file_count=len(files)+2,pins_sha256=sha(b),pins_bytes=len(b),report_sha256=sha((out/'report.txt').read_bytes()),source_index_sha256=sha((out/'source-pins.json').read_bytes()),source_count=len(idx['sources']),cut_count=len(idx['cuts']),cut_lines=sum(c['end']-c['start']+1 for c in idx['cuts']),contract_comparison_sha256=sha((out/'contracts/comparison.json').read_bytes()),family_comparison_sha256=sha((out/'root-family-review/independent-comparison.json').read_bytes()),compiler_checks_executed_by_this_review=0)
(out/'FROZEN.json').write_text(json.dumps(frozen,indent=2)+'\n')
assert len([p for p in out.rglob('*') if p.is_file()])==len(files)+2
for name,pin in files.items():assert sha((out/name).read_bytes())==pin['sha256']
print(json.dumps(dict(**frozen,frozen_sha256=sha((out/'FROZEN.json').read_bytes())),indent=2))
