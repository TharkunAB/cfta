from pathlib import Path
import json,hashlib,subprocess
r=Path('/home/tritlo/Code/mcfta');w=Path(__file__).parent;b=w.parent;base='8e1ea360c6b05c6da1dbb62ac2f9ada4d4d5f0da'
def git(*args,input=None):return subprocess.check_output(['git',*args],cwd=r,input=input)
assert git('rev-parse','HEAD').decode().strip()==base
pub=b/'20261116-writer-and-held-fragment-history-publication';result=json.loads((pub/'checked.json').read_text());assert len(result['checks'])==5 and result['individual_reports']==514 and result['independent_reports']==109 and result['owner_resource_probes']==143
assert all(c['exit']==0 and not c['nonstandard_axioms'] for c in result['checks'])
for name,digest in json.loads((pub/'source-pins.json').read_text()).items():assert hashlib.sha256((r/name).read_bytes()).hexdigest()==digest,name
subprocess.run(['git','diff','--cached','--quiet'],cwd=r,check=True)
audit='lean/MicroCFTA/Audit.lean';old=git('show',base+':'+audit);final=(r/audit).read_bytes();assert final.count(old)==1
opaque='lean/MicroCFTA/SourcePruningEnumerationOpaqueSuffixIsolation.lean';resource='lean/MicroCFTA/SourcePruningEnumerationSharedEagerReservation.lean';writer='lean/MicroCFTA/SourcePruningEnumerationSharedIncomingWriterHistory.lean'
for path in [opaque,resource]:assert (r/path).read_bytes().startswith(git('show',base+':'+path))
probes=[(b/folder/'PROBES.lean.txt').read_bytes().strip()+b'\n' for folder in ['20261116-current-held-fragment-history-owner-assembly','20261116-current-held-fragment-history-projection-owner-assembly']]
firstAudit=old+b'\n'+b'\n'.join(probes)
partial=(b/'20261116-current-tuple-finalize-held-history-assembled/SourcePruningEnumerationSharedEagerReservation.lean').read_bytes();assert (r/resource).read_bytes().startswith(partial)
specs=[('Track held fragment history through state frames',[(opaque,(r/opaque).read_bytes()),(audit,firstAudit)]),('Carry incoming writer history through actual enabled checks',[(writer,(r/writer).read_bytes()),(audit,final)]),('Retain actual tuple fragment history across finalization',[(resource,partial)]),('Derive authentic captured history through native callbacks',[(resource,(r/resource).read_bytes())])];commits=[]
for title,items in specs:
 for path,data in items:
  blob=git('hash-object','-w','--stdin',input=data).decode().strip();git('update-index','--add','--cacheinfo','100644,'+blob+','+path)
 assert set(git('diff','--cached','--name-only').decode().splitlines())=={p for p,_ in items}
 subprocess.run(['git','commit','-m',title],cwd=r,check=True,stdout=subprocess.DEVNULL);commits.append({'title':title,'commit':git('rev-parse','HEAD').decode().strip()})
subprocess.run(['git','diff','--quiet','--',audit,opaque,resource,writer],cwd=r,check=True)
report={'source_commits':commits,'checked_code':commits[-1]['commit'],'public_gates':5,'source_files':6171,'direct_audit_imports':5171,'explicit_reports':514,'independent_reports':109,'original_resource_reports':136,'private_resource_reports':7,'audited_dependencies':result['audited_theorems'],'new_modules_since_50fc':2,'new_public_reports_since_50fc':7,'actual_performed_phase_history_proved':True,'concrete_fragment_history_composition_and_projection_proved':True,'private_tuple_captured_and_callback_components_proved':True,'genuine_depth_IH_is_internal_component_input':True,'whole_worker_906_proved':False,'resource_header_5493_unchanged':True,'runtime_fuels_unchanged':True,'joint_full_history_proved':False,'haskell_changed':False};(w/'WRITER-HELD-SOURCE-COMMITS.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report))
