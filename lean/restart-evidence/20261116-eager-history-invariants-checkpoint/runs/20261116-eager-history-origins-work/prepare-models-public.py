from pathlib import Path
import ast,json,subprocess
w=Path(__file__).parent;r=w.parents[2];b=w.parent
specs=[('SourceSynthesisCurrentRealDoneAssignmentNoneBuckets','20261116-current-real-done-assignment-none-producer-draft','PROBES.lean.txt'),('SourceCurrentAllocatedNativeSourceWarmEntry','20261116-current-source-warm-authentic-entry-draft','PROBES.lean.txt'),('SourceSynthesisCurrentRealDoneRendering','20261116-current-real-done-rendering-source-corollary-draft','PROBES.lean.txt'),('SourceSynthesisCurrentParkedArrowDoneAssignment','20261116-current-source-parked-arrow-done-assignment-clear-namespace-repair','PROBES.lean.txt'),('SourceCurrentAllocatedNativeStoredDispatchReturnedWarmEntry','20261116-current-stored-dispatch-returned-warm-entry-draft','PROBES.lean.txt'),('SourceCurrentAllocatedNativeNodeReturnOrigin','20261116-current-stored-dispatch-returned-warm-entry-draft','RETURN-ORIGIN-PROBES.lean.txt'),('SourceCurrentAllocatedNativeNodeQueryDispatchOrigin','20261116-current-stored-dispatch-returned-warm-entry-draft','WARM-DISPATCH-PROBES.lean.txt')]
laws=[]
for module,folder,probe in specs:
 assert (r/'lean/MicroCFTA'/(module+'.lean')).read_bytes()==(b/folder/(module+'.lean')).read_bytes()
 laws.extend(line.split()[2] for line in (b/folder/probe).read_text().splitlines() if line.startswith('#print axioms '))
assert len(laws)==9
s=(w/'prepare-public-generated.py').read_text();s=s.replace('20261116-eager-history-invariants-publication','20261116-current-source-models-and-warm-admission-publication').replace("prefix='mcfta-eager-history-publication-'","prefix='mcfta-current-models-warm-publication-'")
s=s.replace("changed={'lean/MicroCFTA/Audit.lean'}", "changed={'lean/MicroCFTA/Audit.lean','lean/MicroCFTA/SourceCurrentAllocatedNativeNodeReturnOrigin.lean','lean/MicroCFTA/SourceCurrentAllocatedNativeNodeQueryDispatchOrigin.lean'}")
s=s.replace('assert unchanged==6155','assert unchanged==6153')
s=s.replace("owner=root/", "for name in sorted(changed - {'lean/MicroCFTA/Audit.lean'}):\n    previous=subprocess.check_output(['git','show','ac3fed1766f805c7f355db1bb010d42d32cbf2c6:'+name],cwd=root)\n    assert (root/name).read_bytes().startswith(previous),name\nowner=root/",1)
s=s.replace('import tempfile','import tempfile\nimport subprocess')
lines=s.splitlines(keepends=True)
for i,line in enumerate(lines):
 if line.startswith('modules='):lines[i]='modules='+repr(ast.literal_eval(line.split('=',1)[1])+[x[0] for x in specs])+'\n'
 elif line.startswith('laws='):lines[i]='laws='+repr(ast.literal_eval(line.split('=',1)[1])+laws)+'\n'
 elif line.startswith("text='import "):lines[i]='text='+repr(''.join('import MicroCFTA.'+x[0]+'\n' for x in specs))+'\ntext+='+line[len('text='):]
s=''.join(lines)
for old,new in [('==83','==92'),("'independent_reports':83","'independent_reports':92"),('488','497'),('6160','6165'),('5160','5165'),("'new_public_theorems':4","'new_public_theorems':13"),("'old_non_audit_sources_byte_exact':6155","'old_non_audit_sources_byte_exact':6153"),("'PUBLIC-API-COMPATIBILITY.json'","'MODELS-PUBLIC-API-COMPATIBILITY.json'")]:
 assert old in s,old;s=s.replace(old,new)
s=s.replace("str(independent),64)","str(independent),92)")
s=s.replace("'retained_core_obligations_guardsHold_proved':False,", "'retained_core_obligations_guardsHold_proved':False,'actual_source_current_rendered_satisfies_with_checked_residuals_proved':True,'source_pending_boundary_atom_OnlyU_is_explicit':True,'source_pending_Profile_closure_proved':False,'source_factory_None_supplier_removed':True,'actual_warm_entry_and_return_admission_proved':True,'one_removed_arrow_bucket_same_assignment_proved':True,'all_removed_history_joint_proved':False,")
(w/'prepare-models-public-generated.py').write_text(s)
print(json.dumps({'new_modules_since_ac3':9,'new_reports_since_ac3':13,'owners_exact_prefixes':2,'expected_total_reports':497,'independent_reports':92}))
