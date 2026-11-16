from pathlib import Path
import ast,json
w=Path(__file__).parent;r=w.parents[2];b=w.parent
specs=[('SourcePruningEnumerationSharedPreparedRawPathCongruence','20261116-current-prepared-child-raw-path-congruence-projection-repair','PROBES.lean.txt'),('SourcePruningEnumerationNativeRequestInputs','20261116-current-original-budget-native-admission-proof-draft','OWNER-PROBES.lean.txt'),('SourcePruningEnumerationNativeRequestFields','20261116-current-original-budget-native-admission-proof-draft','PROBES.lean.txt')]
laws=[]
for name,folder,probe in specs:
 p=b/folder;assert (r/'lean/MicroCFTA'/(name+'.lean')).read_bytes()==(p/(name+'.lean')).read_bytes();laws.extend(l.split()[2] for l in (p/probe).read_text().splitlines() if l.startswith('#print axioms '))
assert len(laws)==5
s=(w/'prepare-public-generated.py').read_text().replace('20261116-warm-edge-and-recompletion-publication','20261116-native-admission-and-parent-path-publication').replace("prefix='mcfta-warm-edge-publication-'","prefix='mcfta-native-admission-parent-publication-'")
i=s.index('changed=');j=s.index('\nunchanged=',i);s=s[:i]+"changed={'lean/MicroCFTA/Audit.lean','lean/MicroCFTA/SourceCurrentAllocatedNativeEdgeReturnOrigin.lean','lean/MicroCFTA/SourceCurrentAllocatedNativeEdgeQueryDispatchOrigin.lean','lean/MicroCFTA/SourceCurrentAllocatedNativeSourceIssuedDomainEnterOrigin.lean','lean/MicroCFTA/SourcePruningEnumerationNativeRequestInputs.lean'}"+s[j:]
lines=s.splitlines(keepends=True)
for i,line in enumerate(lines):
 if line.startswith('modules='):
  modules=ast.literal_eval(line.split('=',1)[1]);lines[i]='modules='+repr(modules+[n for n,_,_ in specs if n not in modules])+'\n'
 elif line.startswith('laws='):lines[i]='laws='+repr(ast.literal_eval(line.split('=',1)[1])+laws)+'\n'
 elif line.startswith("text='import "):lines[i]='text='+repr(''.join('import MicroCFTA.'+n+'\n' for n,_,_ in specs))+'\ntext+='+line[len('text='):]
s=''.join(lines)
for a,c in [('assert unchanged==6161','assert unchanged==6160'),('==97','==102'),("'independent_reports':97","'independent_reports':102"),('str(independent),97)','str(independent),102)'),('502','507'),('6167','6169'),('5167','5169'),("'new_public_theorems':5","'new_public_theorems':10"),("'old_non_audit_sources_byte_exact':6161","'old_non_audit_sources_byte_exact':6160"),("'EDGE-PUBLIC-API-COMPATIBILITY.json'","'NATIVE-PATH-PUBLIC-API-COMPATIBILITY.json'")]:
 assert a in s,a;s=s.replace(a,c)
s=s.replace("'actual_warm_node_and_edge_return_admission_proved':True,","'actual_warm_node_and_edge_return_admission_proved':True,'actual_prepared_parent_path_congruence_proved':True,'original_budget_admitted_physical_and_field_plans_proved':True,")
(w/'prepare-native-path-public-generated.py').write_text(s);print(json.dumps({'new_modules_since_9f':4,'new_reports_since_9f':10,'old_owner_prefixes':4,'expected_reports':507,'independent_reports':102}))
