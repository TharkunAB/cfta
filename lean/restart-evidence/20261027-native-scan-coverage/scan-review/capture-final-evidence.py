from pathlib import Path
import hashlib, json, difflib
repo=Path('/home/tritlo/Code/mcfta'); area=Path('/tmp/mcfta-native-scan-coverage-20261027'); out=area/'scan-review'
sha=lambda b:hashlib.sha256(b).hexdigest()
def put(rel,b):
 p=out/rel; p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b.encode() if isinstance(b,str) else b)
def copy(rel,dest=None):
 b=(area/rel).read_bytes();put(dest or 'evidence/'+rel,b);return b
index=json.loads((out/'source-index.json').read_text())
for row in index['sources']:
 if row['source'].endswith('SourcePruningEnumerationNativeBranchCoverage.lean'):
  old=(out/row['whole']['path']).read_bytes()
  if sha(old)=='11f5681975219ae83917ec2c67fdaf43c3019a7e54b7ba18ba1877948e504630':
   put('reviewed-drafts/source-index-scan-v2-record.json',json.dumps(row,indent=2)+'\n')
  src=Path(row['source']);b=src.read_bytes(); assert sha(b)=='e599f45019d10168ac50ca6f793877bbf22ae840b2f8ca89de89edb3336c91d6'
  put(row['whole']['path'],b);row['whole'].update(bytes=len(b),sha256=sha(b));row['review_scope']='Whole final scan V3 reviewed. Only proof repair from preserved V2: Or.inl rfl becomes Or.inl trivial after simplification. Header unchanged.'
  for cut in row['cuts']:
   c=b''.join(b.splitlines(keepends=True)[cut['first_line']-1:cut['last_line']]);put(cut['path'],c);cut.update(bytes=len(c),sha256=sha(c))
  put('reviewed-drafts/scan-v3.lean',b)
  before=(out/'reviewed-drafts/scan-v2.lean').read_text();after=b.decode()
  put('reviewed-drafts/scan-v2-v3.diff',''.join(difflib.unified_diff(before.splitlines(True),after.splitlines(True),fromfile='scan-v2.lean',tofile='scan-v3.lean')))
name='SourcePruningEnumerationNativeParentCoverage.lean';src=repo/'lean/MicroCFTA'/name;b=src.read_bytes()
assert sha(b)=='faa1342a9e174a9a61ba826a55fb0c6646eb4e4f318324e42cd8dc8fc4647cd9'
whole='sources/'+name;cut='cuts/'+name+'.1-205.txt';put(whole,b);put(cut,b)
row={'source':str(src),'whole':{'path':whole,'bytes':len(b),'sha256':sha(b)},'review_scope':'Whole parent-facing wrapper reviewed. Original stored model and selected permutation derive accepting occurrence; explicit original all-selected support implies aggregate completion. One actual primary call. Chosen local endpoint remains separate.','cuts':[{'path':cut,'bytes':len(b),'sha256':sha(b),'first_line':1,'last_line':205}]}
index['sources']=[r for r in index['sources'] if r['source']!=str(src)]+[row]
put('source-index.json',json.dumps(index,indent=2)+'\n');put('reviewed-drafts/parent-v1.lean',b)
def proposition(name,theorem):
 s=(repo/'lean/MicroCFTA'/name).read_text();return s[s.index('theorem '+theorem+'\n'):].split(' := by\n',1)[0]
primary=proposition('SourcePruningEnumerationNativeBranchCoverage.lean','complete_with_history_resources_accepting')
parent=proposition(name,'parent_complete_resources')
start='    ∃ (r n p h k : Nat)'
oldresult=primary[primary.index(start):]
newresult=parent[parent.index(start):].split(') ∧\n      result = .complete processed afterCaller saved ∧\n      ∃ (index',1)[0]
recovered=newresult.replace('      ((∀ er en P H ek,','      (∀ er en P H ek,',1)
assert recovered==oldresult
put('contracts/ParentCoverage.primary-entire-result.txt',oldresult);put('contracts/ParentCoverage.recovered-entire-result.txt',recovered)
put('contracts/ParentCoverage.comparison.json',json.dumps({'status':'PASS','entire_primary_result_bytes':len(oldresult.encode()),'entire_primary_result_sha256':sha(oldresult.encode()),'mapping':'Remove appended aggregate-complete and chosen-receipt clauses; remove the extra grouping parenthesis. Every original primary result field, including its uniform indexed observer, is unchanged.','input_changes':'Perm replaces subset. Add explicit original all-selected support and an original satisfying model. Derive subset from Perm. No supplied accepting edge/index or future invocation.'},indent=2)+'\n')
checks=[]
for check,module,expected in [('strict-head-1','SourcePruningEnumerationNativeHeadCoverage',0),('strict-scan-1','SourcePruningEnumerationNativeBranchCoverage',1),('strict-scan-2','SourcePruningEnumerationNativeBranchCoverage',0),('strict-parent-1','SourcePruningEnumerationNativeParentCoverage',0),('strict-audit-1','Audit',0)]:
 r=json.loads(copy(check+'/report.json'));raw=copy(check+'/raw.log');snap=copy(check+'/MicroCFTA/'+module+'.lean')
 assert r['exit_code']==expected and r['bytes']==len(raw) and r['sha256']==sha(raw) and r['source_sha256']==sha(snap)
 assert r['cgroup_limits']=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
 if check!='strict-scan-1': assert snap==(repo/'lean/MicroCFTA'/f'{module}.lean').read_bytes()
 checks.append({'check':check,'expected_exit':expected,'verified_raw_bytes':len(raw),'source_sha256':sha(snap),'installed_identical':check!='strict-scan-1'})
for check in ['build-head-1','build-scan-1','audit-1','public-readback-1']:
 r=json.loads(copy(check+'/report.json'));raw=copy(check+'/raw.log');assert r['exit_code']==0 and r['bytes']==len(raw) and r['sha256']==sha(raw)
 checks.append({'check':check,'exit_code':0,'verified_raw_bytes':len(raw),'raw_sha256':sha(raw)})
for rel in ['scan-prefix-membership-repair.json','source-validation.json','preservation-validation.json','packet-comparison.json','strict-checks.json','new-source-totals.json','modules.json','audit-import-insertion.json','public-declarations.json','public-definitions.json']:
 if (area/rel).exists():copy(rel)
put('evidence/independent-check-binding.json',json.dumps({'status':'PASS','checks':checks,'compiler_run_by_reviewer':False,'build_run_by_reviewer':False},indent=2)+'\n')
put('reviewed-drafts/status.json',json.dumps({'status':'OPEN','head_v1_sha256':sha((out/'reviewed-drafts/head-v1.lean').read_bytes()),'scan_v2_sha256':sha((out/'reviewed-drafts/scan-v2.lean').read_bytes()),'scan_final_v3_sha256':sha((out/'reviewed-drafts/scan-v3.lean').read_bytes()),'parent_v1_sha256':sha(b),'proof_review':'CLEAR. Final source checks, builds and raw evidence verified. Public signature and final prose review remain open.'},indent=2)+'\n')
print(json.dumps({'status':'PASS','source_records':len(index['sources']),'cuts':sum(len(r['cuts']) for r in index['sources']),'checks':len(checks),'primary_entire_result_bytes':len(oldresult.encode())}))
