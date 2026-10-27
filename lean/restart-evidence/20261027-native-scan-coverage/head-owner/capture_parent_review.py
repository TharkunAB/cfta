from pathlib import Path
import json,hashlib,datetime,difflib
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
for check in ['strict-scan-2','build-scan-1','strict-parent-1']:
 r=json.loads((stage/check/'report.json').read_text());raw=(stage/check/'raw.log').read_bytes()
 assert r['exit_code']==0 and ident(raw)=={'bytes':r['bytes'],'sha256':r['sha256']}
 assert r['cgroup_limits']=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
 for name in ['report.json','raw.log']:cap(stage/check/name,f'checks/{check}/{name}')
 if check.startswith('strict'):
  mod='SourcePruningEnumerationNativeBranchCoverage' if check=='strict-scan-2' else 'SourcePruningEnumerationNativeParentCoverage'
  p=stage/check/'MicroCFTA'/f'{mod}.lean';assert ident(p.read_bytes())['sha256']==r['source_sha256']
  assert p.read_bytes()==(root/'lean/MicroCFTA'/f'{mod}.lean').read_bytes()
  cap(p,f'checks/{check}/{mod}.lean')
scan=root/'lean/MicroCFTA/SourcePruningEnumerationNativeBranchCoverage.lean';v3=scan.read_bytes();v2=(a/'scan-review/scan-v2.lean').read_bytes()
assert v3==v2.replace(b'exact .inl rfl) allowed projected',b'exact .inl trivial) allowed projected',1)
def prop(s,name):
 i=s.index('theorem '+name+'\n');return s[i:s.index(' := by',i)]
assert prop(v2.decode(),'complete_with_history_resources_accepting')==prop(v3.decode(),'complete_with_history_resources_accepting')
cap(scan,'scan-review/scan-v3-final.lean',[(36,126),(233,313)])
(a/'scan-review/v2-v3.diff').write_text(''.join(difflib.unified_diff(v2.decode().splitlines(keepends=True),v3.decode().splitlines(keepends=True),fromfile='v2-failed',tofile='v3-passed')))
(a/'scan-review/v2-v3-comparison.json').write_text(json.dumps({'status':'PASS','only_change':'One final Or.inl proof uses trivial instead of rfl after simplification produced True.','v2':ident(v2),'v3':ident(v3),'public_statement_literal_equal':True},indent=2)+'\n')
parent=root/'lean/MicroCFTA/SourcePruningEnumerationNativeParentCoverage.lean';pb=parent.read_bytes()
assert pb==(stage/'parent/drafts/v1/SourcePruningEnumerationNativeParentCoverage.lean').read_bytes()
assert ident(pb)['sha256']=='faa1342a9e174a9a61ba826a55fb0c6646eb4e4f318324e42cd8dc8fc4647cd9'
cap(parent,'parent-review/whole/SourcePruningEnumerationNativeParentCoverage.lean',[(38,167),(168,203)])
p=prop(v3.decode(),'complete_with_history_resources_accepting');w=prop(pb.decode(),'parent_complete_resources')
preturn=p[p.index('    ∃ (r n p h k : Nat)'):]
start=w.index('    ∃ (r n p h k : Nat)')
marker='              extended afterCache.core) ∧\n      result = .complete processed afterCaller saved ∧'
end=w.index(marker,start)+len('              extended afterCache.core')
recovered=w[start:end].replace('      ((∀ er en P H ek,','      (∀ er en P H ek,',1)
assert preturn==recovered
cc=a/'parent-review/contract-comparison';cc.mkdir(parents=True,exist_ok=True)
for name,s in [('primary-entire-result.txt',preturn),('wrapper-recovered-entire-result.txt',recovered),('wrapper-full-statement.txt',w)]: (cc/name).write_text(s)
(cc/'comparison.json').write_text(json.dumps({'status':'PASS','recovery':'Delete only wrapper grouping, chosen complete-scan conclusion and concrete chosen-index appendix. Entire primary existential/result/universal observer recover literally. No header identity claim for the semantic-facing wrapper.','primary':ident(preturn.encode()),'recovered':ident(recovered.encode()),'wrapper_statement':ident(w.encode())},indent=2)+'\n')
(a/'source-index.json').write_text(json.dumps(idx,indent=2)+'\n')
(a/'parent-review/report.txt').write_text(f'''CLEAR — full independent NativeParentCoverage review\n\nMeasured time: {datetime.datetime.now().astimezone().isoformat()}\nFull source: 205 lines, 14257 bytes, SHA256 faa1342a9e174a9a61ba826a55fb0c6646eb4e4f318324e42cd8dc8fc4647cd9. Draft, installed and strict-parent-1 source bytes are identical. Actual first strict check PASS, exit 0/raw 0, measured 4 GiB memory.max/high and zero swap.\n\nThe original stored pending Satisfies model yields parent acceptance via actual decoded handle. Perm supplies an actual selected edge that accepts assignment uv and a concrete selected-list index. The wrapper assumes support for ALL selected arity-allowed edges; this is explicitly stronger than the primary observer's support of ONLY the prefix before its chosen index. ALL support supplies both the prefix observer gate and exact whole NativeBranches scan completion. It remains an original current-list/pure-projection property, not a future invocation or semantic outcome.\n\nThe rich primary scan producer is invoked ONCE. The entire primary existential/result packet, all old resource/history fields and its universal indexed observer are retained under explicit grouping. Literal result recovery after removing only grouping and the concrete wrapper appendices is recorded in contract-comparison/. No claim is made that the stronger semantic-facing wrapper's header matches the primary. Chosen original model precedes the chosen operational bounds. The retained primary observer is universal after those bounds.\n\nThe chosen occurrence is in the SAME processed list at its SAME index. Its actual captured call runs at the SAME global scan bound family. Head input Caller/Inventory/full headMemos, local branch Caller/full branchMemos/query equality, aggregate original-to-head Post and local head-to-branch Post are retained distinctly. Final cache Satisfies uses the chosen branch's OWN native heap, not an unrelated later aggregate scan endpoint. Original assignment agreement and original-state satisfaction remain part of the constructed witness. Duplicate edges retain their actual list indices.\n\nScope is NativeBranches, whose advance continues rejected and valid child-rejected receipts. No recursive NativeContinuations hook completion or whole recursive coverage follows. The full-list support assumption excludes unsupported NativeBranches heads, but does not exclude or analyze separate recursive hook stops. Discharged/rendering coverage, frontier policy and physical Haskell correspondence remain open. No future successful scan or desired final model is supplied as admission. Bundle OPEN for final Audit/public/docs.\n''')
(a/'scan-review/report-v2-source-review.txt').write_bytes((a/'scan-review/report.txt').read_bytes())
s=(a/'scan-review/report.txt').read_text();s+='''\nAuthoritative checked final source\nRoot v3 changes ONLY the final .inl rfl to .inl trivial. The full public statement is literally unchanged. strict-scan-2 passes exit 0/raw 0 on exact final SHA256 e599f45019d10168ac50ca6f793877bbf22ae840b2f8ca89de89edb3336c91d6. Strict source and installed source are identical. build-scan-1 passes 1906 jobs; exact raw contains the known old dependency warning. Both failed and successful strict sources/reports/raw remain. No check was run by this worker. Source and result-scope review remains CLEAR; final Audit/public/docs pending.\n''';(a/'scan-review/report.txt').write_text(s)
print(json.dumps({'scan_final':'PASS proof-only v3','parent_review':'CLEAR / first strict PASS','entire_primary_result':ident(preturn.encode()),'source_records':len(idx['sources'])},indent=2))
