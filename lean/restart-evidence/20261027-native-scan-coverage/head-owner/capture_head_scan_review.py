from pathlib import Path
import json,hashlib,datetime
root=Path('/home/tritlo/Code/mcfta');stage=Path('/tmp/mcfta-native-scan-coverage-20261027');a=stage/'head-owner'
def ident(b):return {'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}
idx=json.loads((a/'source-index.json').read_text())
def cap(p,rel,cuts=()):
 b=p.read_bytes();dest=Path(rel);(a/dest).parent.mkdir(parents=True,exist_ok=True);(a/dest).write_bytes(b)
 r={'source':str(p),'whole':{'path':str(dest),**ident(b)},'cuts':[]};lines=b.splitlines(keepends=True)
 for first,last in cuts:
  cb=b''.join(lines[first-1:last]);cp=dest.parent/(dest.name+f'.L{first}-L{last}.txt');(a/cp).write_bytes(cb)
  r['cuts'].append({'path':str(cp),**ident(cb),'first_line':first,'last_line':last})
 idx['sources'].append(r)
for check in ['strict-head-1','build-head-1','strict-scan-1']:
 rp=stage/check/'report.json';r=json.loads(rp.read_text());raw=(stage/check/'raw.log').read_bytes()
 assert ident(raw)=={'bytes':r['bytes'],'sha256':r['sha256']}
 for name in ['report.json','raw.log']:cap(stage/check/name,f'checks/{check}/{name}')
 if check.startswith('strict'):
  mod='SourcePruningEnumerationNativeHeadCoverage' if check=='strict-head-1' else 'SourcePruningEnumerationNativeBranchCoverage'
  p=stage/check/'MicroCFTA'/f'{mod}.lean';assert ident(p.read_bytes())['sha256']==r['source_sha256']
  cap(p,f'checks/{check}/{mod}.lean')
  if check=='strict-head-1':assert p.read_bytes()==(a/'drafts/v1'/f'{mod}.lean').read_bytes()==(root/'lean/MicroCFTA'/f'{mod}.lean').read_bytes()
scan=stage/'scan-owner/drafts/v2/SourcePruningEnumerationNativeBranchCoverage.lean'
cap(scan,'scan-review/scan-v2.lean',[(36,126),(139,174),(233,313)])
cap(root/'lean/MicroCFTA/SourcePruningEnumerationNativeLanguage.lean','scan-review/NativeLanguage.lean',[(86,98)])
s=scan.read_text();old=(root/'lean/MicroCFTA/SourcePruningEnumerationNativeBranchResources.lean').read_text()
def prop(s,name):
 i=s.index('theorem '+name+'\n');return s[i:s.index(' := by',i)]
p=prop(old,'complete_with_history_resources');n=prop(s,'complete_with_history_resources_accepting')
marker=' ∧\n      ∀ (index : Nat) (chosen : EdgeValue Symbol Constraint),'
recovered=n[:n.index(marker)].replace('theorem complete_with_history_resources_accepting\n','theorem complete_with_history_resources\n',1)
assert p==recovered
cc=a/'scan-review/contract-comparison';cc.mkdir(parents=True,exist_ok=True)
for name,text in [('old-full-contract.txt',p),('new-full-contract.txt',n),('recovered-old-full-contract.txt',recovered)]: (cc/name).write_text(text)
(cc/'comparison.json').write_text(json.dumps({'status':'PASS','recovery':'Remove only final indexed accepting observer and reverse theorem name. The ENTIRE old admission, witnesses and result are literal.','old':ident(p.encode()),'new':ident(n.encode()),'recovered':ident(recovered.encode())},indent=2)+'\n')
(a/'source-index.json').write_text(json.dumps(idx,indent=2)+'\n')
(a/'scan-review/report.txt').write_text(f'''CLEAR — full independent source review of NativeBranchCoverage v2\n\nMeasured time: {datetime.datetime.now().astimezone().isoformat()}\nWhole source: 314 lines, 21683 bytes, SHA256 11f5681975219ae83917ec2c67fdaf43c3019a7e54b7ba18ba1877948e504630. Root's first strict check failed ONLY the final unhandled/successor head-membership simplification, where Or.inl expects True and rfl is given. Exact failed source/report/raw are retained. No successful strict claim is made for v2. Suggested repair sent to Root: replace ONLY final .inl rfl by .inl trivial.\n\nThe complete old scan contract is preserved literally after deleting only the final indexed observer and reversing the public theorem name; full propositions and comparison are retained. No original admission or result field is removed. The new observer follows global operational bounds and the full result packet. It quantifies an ORIGINAL selected index and original support of ONLY selectedEdges.take index, then an original satisfying assignment and acceptance by that SAME indexed edge at assignment uv. No future caller, invocation or successful output is supplied.\n\nThe cons induction invokes the rich head producer once, derives actual native Keeps/full returned Context, transfers realized and candidate facts at SAME restored captured cache, and invokes the suffix at the real middleCaller and full middleMemos. Reservation prefix/after_prefix and forecast padding match the actual old cost. Global bounds are r+tr, n+tn, max p tp, max h th, k+tk; both actual head and chosen suffix stable families are shifted to those SAME bounds. Query equality is used only to connect actual calls; full input headMemos and local branchMemos remain distinct named witnesses and both exact Post receipts are retained.\n\nIndex zero uses the actual head accepting observer, places its complete receipt at processed[0] and retains its actual captured run at all global adequate bounds. A later suffix can still stop; the completed head receipt remains in processed. Successor index derives support for the tail's original prefix, transports original Satisfies to middleHeap with satisfies_keeps.mpr, and transports the extended original-state model back with .mp. Both directions use the original realized state and actual headPost.effects.keeps. Independent native edgeMeaning has no heap argument and is retained literally. Input Post composes headPost before tail inputPost; local branch Post and full branchMemos are preserved unchanged.\n\nUnhandled-head index zero contradicts the actual accepting head observer. A positive index has the actual unsupported head in its original take-prefix, contradicting the supplied original support. No future projection gate is introduced. Rejected and child-rejected continuable receipts keep their actual native endpoints; no Safe-on-rejection inference is used. All old stopped outputs, processed receipt histories, per-index resource forecasts and aggregate Post/full Memos remain.\n\nScope: this is actual NativeBranches coverage through a supported original prefix, not coverage of NativeContinuations hooks or the complete recursive enumerator. Unsupported-prefix support remains an explicit observer condition. Entire-scan completion is not needed for an earlier accepting receipt to be retained. No compiler, build, repository or external action was run by this worker. Bundle OPEN until Root's repaired strict source and final integration/public/docs.\n''')
(a/'report-initial.txt').write_bytes((a/'report.txt').read_bytes())
s=(a/'report.txt').read_text().replace('Status: OPEN / UNTESTED. Root owns all compiler, build, repository, Git, network and publication actions. This worker ran no compiler, evaluator, build or native test.','Status: OPEN / HEAD STRICT PASS. Root strict-head-1 passes the unchanged v1 with zero raw output at actual 4 GiB memory.max/high and zero swap. Draft, strict source and installed source match literally. build-head-1 passes 1905 jobs. The initial untested report is preserved in report-initial.txt. Root owns all compiler, build, repository, Git, network and publication actions. This worker ran no compiler, evaluator, build or native test.')
s+='\nIndependent scan review\nFull NativeBranchCoverage v2 was read independently. Its semantics and complete old contract retention are CLEAR, pending Root repair of one terminal proof elaboration. The actual first strict failure is retained honestly, with no successful v2 claim. See scan-review/report.txt and contract comparison. Final repaired source, installed Audit/public and documentation evidence remain pending.\n'
(a/'report.txt').write_text(s)
print(json.dumps({'head':'PASS unchanged','scan_v2':'source CLEAR / strict FAIL retained','scan_old_contract':ident(p.encode()),'records':len(idx['sources'])},indent=2))
