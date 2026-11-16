from pathlib import Path
import json,hashlib,subprocess
r=Path('/home/tritlo/Code/mcfta');w=Path(__file__).parent;b=w.parent;base='50fc53f75647f2b141cdddc578e75756e675dccc'
def git(*args,input=None):return subprocess.check_output(['git',*args],cwd=r,input=input)
assert git('rev-parse','HEAD').decode().strip()==base
pub=b/'20261116-incoming-history-and-local-finalize-publication';result=json.loads((pub/'checked.json').read_text());assert len(result['checks'])==5 and result['individual_reports']==509 and result['independent_reports']==104 and result['owner_resource_probes']==137
assert all(c['exit']==0 and not c['nonstandard_axioms'] for c in result['checks'])
for name,digest in json.loads((pub/'source-pins.json').read_text()).items():assert hashlib.sha256((r/name).read_bytes()).hexdigest()==digest,name
subprocess.run(['git','diff','--cached','--quiet'],cwd=r,check=True)
audit='lean/MicroCFTA/Audit.lean';old=git('show',base+':'+audit);final=(r/audit).read_bytes();assert final.count(old)==1
specs=[('Expose the exact state transition of a successful finalizer','SourcePruningEnumerationOpaqueSuffixIsolation','20261116-current-tuple-finalize-avoidance-assembled','ALIAS-PROBES.lean.txt',False),('Derive prepared incoming query history from actual success','SourcePruningEnumerationSharedIncomingQueryHistory','20261116-current-prepared-shared-incoming-query-history-draft','PROBES.lean.txt',True),('Derive pending-target avoidance through actual tuple finalization','SourcePruningEnumerationSharedEagerReservation','20261116-current-tuple-finalize-avoidance-assembled',None,False)]
imports=[];probes=[];commits=[]
for index,(title,module,folder,probe,new) in enumerate(specs):
 name='lean/MicroCFTA/'+module+'.lean';assert (r/name).read_bytes()==(b/folder/(module+'.lean')).read_bytes();paths=[name]
 if probe:
  if new:imports.append('import MicroCFTA.'+module+'\n')
  probes.append((b/folder/probe).read_bytes().strip()+b'\n')
  staged=final if index==1 else ''.join(imports).encode()+old+b'\n'+b'\n'.join(probes)
  blob=git('hash-object','-w','--stdin',input=staged).decode().strip();git('update-index','--add','--cacheinfo','100644,'+blob+','+audit);paths.append(audit)
 subprocess.run(['git','add','-f','--',name],cwd=r,check=True)
 assert set(git('diff','--cached','--name-only').decode().splitlines())==set(paths)
 subprocess.run(['git','commit','-m',title],cwd=r,check=True,stdout=subprocess.DEVNULL)
 commits.append({'title':title,'commit':git('rev-parse','HEAD').decode().strip()})
subprocess.run(['git','diff','--quiet','--',audit],cwd=r,check=True)
report={'source_commits':commits,'checked_code':commits[-1]['commit'],'public_gates':5,'source_files':6170,'direct_audit_imports':5170,'explicit_reports':509,'independent_reports':104,'original_resource_reports':136,'private_resource_reports':1,'audited_dependencies':result['audited_theorems'],'new_modules_since_50fc':1,'new_public_reports_since_50fc':2,'actual_prepared_incoming_history_proved':True,'private_tuple_finalize_avoidance_proved':True,'whole_worker_906_proved':False,'resource_header_5493_unchanged':True,'runtime_fuels_unchanged':True,'joint_full_history_proved':False,'haskell_changed':False};(w/'SOURCE-COMMITS.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report))
