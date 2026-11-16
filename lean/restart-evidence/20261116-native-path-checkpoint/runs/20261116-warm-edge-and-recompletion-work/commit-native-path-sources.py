from pathlib import Path
import json,hashlib,subprocess
r=Path('/home/tritlo/Code/mcfta');w=Path(__file__).parent;b=w.parent;base='3c9f70a21a1d06764cca98695ecbceadedab61de'
def git(*args,input=None):return subprocess.check_output(['git',*args],cwd=r,input=input)
assert git('rev-parse','HEAD').decode().strip()==base
pub=b/'20261116-native-admission-and-parent-path-publication';result=json.loads((pub/'checked.json').read_text());assert len(result['checks'])==5 and result['individual_reports']==507 and result['independent_reports']==102
assert all(c['exit']==0 and not c['nonstandard_axioms'] for c in result['checks'])
for name,digest in json.loads((pub/'source-pins.json').read_text()).items():assert hashlib.sha256((r/name).read_bytes()).hexdigest()==digest,name
subprocess.run(['git','diff','--cached','--quiet'],cwd=r,check=True)
audit='lean/MicroCFTA/Audit.lean';old=git('show',base+':'+audit);final=(r/audit).read_bytes();assert final.count(old)==1
specs=[('Derive parent-path target congruence from actual child returns',[('SourcePruningEnumerationSharedPreparedRawPathCongruence','20261116-current-prepared-child-raw-path-congruence-projection-repair','PROBES.lean.txt',True)]),('Expose original-budget input plans from actual completed traces',[('SourcePruningEnumerationNativeRequestInputs','20261116-current-original-budget-native-admission-proof-draft','OWNER-PROBES.lean.txt',False)]),('Derive native input and field plans from current admission',[('SourcePruningEnumerationNativeRequestFields','20261116-current-original-budget-native-admission-proof-draft','PROBES.lean.txt',True)])]
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
 assert set(git('diff','--cached','--name-only').decode().splitlines())==set(paths+[audit])
 subprocess.run(['git','commit','-m',title],cwd=r,check=True,stdout=subprocess.DEVNULL)
 commits.append({'title':title,'commit':git('rev-parse','HEAD').decode().strip()})
subprocess.run(['git','diff','--quiet','--',audit],cwd=r,check=True)
report={'source_commits':commits,'checked_code':commits[-1]['commit'],'public_gates':5,'source_files':6169,'explicit_reports':507,'independent_reports':102,'audited_dependencies':result['audited_theorems'],'new_modules_since_3c9':2,'new_public_reports_since_3c9':5,'parent_path_congruence_original_header_exact':True,'actual_Admits_Room_or_Entry_covered':True,'runtime_fuels_unchanged':True,'joint_full_history_proved':False,'haskell_changed':False};(w/'NATIVE-PATH-SOURCE-COMMITS.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report))
