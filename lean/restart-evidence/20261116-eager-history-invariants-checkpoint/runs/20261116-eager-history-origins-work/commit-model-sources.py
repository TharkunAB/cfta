from pathlib import Path
import hashlib,json,subprocess
r=Path('/home/tritlo/Code/mcfta');w=Path(__file__).parent;b=w.parent
base='0968da7d14b8233b5cad84c69e1aa2450fa892b7'
def git(*args,input=None):
 return subprocess.check_output(['git',*args],cwd=r,input=input)
assert git('rev-parse','HEAD').decode().strip()==base
public=b/'20261116-current-source-models-and-warm-admission-publication'
result=json.loads((public/'checked.json').read_text())
assert len(result['checks'])==5 and result['individual_reports']==497
assert all(c['exit']==0 and not c['nonstandard_axioms'] for c in result['checks'])
assert result['checks'][2]['total_axiom_reports']==92
for name,digest in json.loads((public/'source-pins.json').read_text()).items():
 assert hashlib.sha256((r/name).read_bytes()).hexdigest()==digest,name
subprocess.run(['git','diff','--cached','--quiet'],cwd=r,check=True)
audit='lean/MicroCFTA/Audit.lean';old=git('show',base+':'+audit);final=(r/audit).read_bytes();assert final.count(old)==1
specs=[
 ('Derive empty pending buckets from the actual source worker',[('SourceSynthesisCurrentRealDoneAssignmentNoneBuckets','20261116-current-real-done-assignment-none-producer-draft','PROBES.lean.txt',True)]),
 ('Recover warm query qualification from actual source entries',[('SourceCurrentAllocatedNativeSourceWarmEntry','20261116-current-source-warm-authentic-entry-draft','PROBES.lean.txt',True)]),
 ('Construct satisfying current assignments from actual rendering',[('SourceSynthesisCurrentRealDoneRendering','20261116-current-real-done-rendering-source-corollary-draft','PROBES.lean.txt',True)]),
 ('Restore a removed arrow bucket under one compatible assignment',[('SourceSynthesisCurrentParkedArrowDoneAssignment','20261116-current-source-parked-arrow-done-assignment-clear-namespace-repair','PROBES.lean.txt',True)]),
 ('Derive retained or locally produced warm cache entries',[('SourceCurrentAllocatedNativeNodeReturnOrigin','20261116-current-stored-dispatch-returned-warm-entry-draft','RETURN-ORIGIN-PROBES.lean.txt',False),('SourceCurrentAllocatedNativeNodeQueryDispatchOrigin','20261116-current-stored-dispatch-returned-warm-entry-draft','WARM-DISPATCH-PROBES.lean.txt',False),('SourceCurrentAllocatedNativeStoredDispatchReturnedWarmEntry','20261116-current-stored-dispatch-returned-warm-entry-draft','PROBES.lean.txt',True)])]
imports=[];probes=[];commits=[]
for index,(title,items) in enumerate(specs):
 paths=[]
 for module,folder,probe,new in items:
  name='lean/MicroCFTA/'+module+'.lean';assert (r/name).read_bytes()==(b/folder/(module+'.lean')).read_bytes();paths.append(name)
  if new:imports.append('import MicroCFTA.'+module+'\n')
  probes.append((b/folder/probe).read_bytes().strip()+b'\n')
 staged=final if index==len(specs)-1 else ''.join(imports).encode()+old+b'\n'+b'\n'.join(probes)
 blob=git('hash-object','-w','--stdin',input=staged).decode().strip();git('update-index','--add','--cacheinfo','100644,'+blob+','+audit)
 subprocess.run(['git','add','-f','--',*paths],cwd=r,check=True)
 names=set(git('diff','--cached','--name-only').decode().splitlines());assert names==set(paths+[audit]),names
 subprocess.run(['git','commit','-m',title],cwd=r,check=True,stdout=subprocess.DEVNULL)
 commits.append({'title':title,'commit':git('rev-parse','HEAD').decode().strip()})
assert (r/audit).read_bytes()==final
subprocess.run(['git','diff','--quiet','--',audit],cwd=r,check=True)
report={'source_commits':commits,'checked_code':commits[-1]['commit'],'public_gates':5,'source_files':6165,'explicit_reports':497,'independent_reports':92,'new_modules_since_0968':5,'new_public_reports_since_0968':9,'old_owner_exact_prefixes':2,'one_removed_arrow_bucket_assignment_proved':True,'joint_full_history_proved':False,'haskell_changed':False}
(w/'MODEL-SOURCE-COMMITS.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report))
