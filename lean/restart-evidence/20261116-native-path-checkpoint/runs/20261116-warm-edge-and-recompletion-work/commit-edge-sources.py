from pathlib import Path
import json,hashlib,subprocess
r=Path('/home/tritlo/Code/mcfta');w=Path(__file__).parent;b=w.parent;p=b/'20261116-current-stored-dispatch-returned-warm-edge-draft';base='9f4ad619d01ec5dd187bb6c25db962c60c558da7'
def git(*args,input=None):return subprocess.check_output(['git',*args],cwd=r,input=input)
assert git('rev-parse','HEAD').decode().strip()==base
pub=b/'20261116-warm-edge-and-recompletion-publication';result=json.loads((pub/'checked.json').read_text());assert len(result['checks'])==5 and result['individual_reports']==502 and result['independent_reports']==97
assert all(c['exit']==0 and not c['nonstandard_axioms'] for c in result['checks'])
for name,digest in json.loads((pub/'source-pins.json').read_text()).items():assert hashlib.sha256((r/name).read_bytes()).hexdigest()==digest,name
subprocess.run(['git','diff','--cached','--quiet'],cwd=r,check=True)
audit='lean/MicroCFTA/Audit.lean';old=git('show',base+':'+audit);final=(r/audit).read_bytes();assert final.count(old)==1
specs=[('Expose actual edge return and warm source provenance',[('SourceCurrentAllocatedNativeEdgeReturnOrigin','EDGE-RETURN-PROBES.lean.txt',False),('SourceCurrentAllocatedNativeEdgeQueryDispatchOrigin','WARM-EDGE-DISPATCH-PROBES.lean.txt',False),('SourceCurrentAllocatedNativeSourceIssuedDomainEnterOrigin','EDGE-DOMAIN-PROBES.lean.txt',False)]),('Derive actual warm source entries for edge requests',[('SourceCurrentAllocatedNativeSourceWarmEdgeEntry','WARM-EDGE-ENTRY-PROBES.lean.txt',True)]),('Classify returned edge entries from actual warm execution',[('SourceCurrentAllocatedNativeStoredDispatchReturnedWarmEdgeEntry','PROBES.lean.txt',True)])]
imports=[];probes=[];commits=[]
for index,(title,items) in enumerate(specs):
 paths=[]
 for module,probe,new in items:
  name='lean/MicroCFTA/'+module+'.lean';assert (r/name).read_bytes()==(p/(module+'.lean')).read_bytes();paths.append(name)
  if new:imports.append('import MicroCFTA.'+module+'\n')
  probes.append((p/probe).read_bytes().strip()+b'\n')
 staged=final if index==len(specs)-1 else ''.join(imports).encode()+old+b'\n'+b'\n'.join(probes)
 blob=git('hash-object','-w','--stdin',input=staged).decode().strip();git('update-index','--add','--cacheinfo','100644,'+blob+','+audit)
 subprocess.run(['git','add','-f','--',*paths],cwd=r,check=True)
 assert set(git('diff','--cached','--name-only').decode().splitlines())==set(paths+[audit])
 subprocess.run(['git','commit','-m',title],cwd=r,check=True,stdout=subprocess.DEVNULL)
 commits.append({'title':title,'commit':git('rev-parse','HEAD').decode().strip()})
subprocess.run(['git','diff','--quiet','--',audit],cwd=r,check=True)
report={'source_commits':commits,'checked_code':commits[-1]['commit'],'public_gates':5,'source_files':6167,'explicit_reports':502,'independent_reports':97,'audited_dependencies':98717,'new_modules':2,'new_public_reports':5,'old_owner_exact_prefixes':3,'joint_full_history_proved':False,'haskell_changed':False};(w/'EDGE-SOURCE-COMMITS.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report))
