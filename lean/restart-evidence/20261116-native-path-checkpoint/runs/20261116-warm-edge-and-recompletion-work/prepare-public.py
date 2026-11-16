from pathlib import Path
import ast,json
w=Path(__file__).parent;r=w.parents[2];b=w.parent;old=b/'20261116-eager-history-origins-work';p=b/'20261116-current-stored-dispatch-returned-warm-edge-draft'
specs=[('SourceCurrentAllocatedNativeEdgeReturnOrigin','EDGE-RETURN-PROBES.lean.txt'),('SourceCurrentAllocatedNativeEdgeQueryDispatchOrigin','WARM-EDGE-DISPATCH-PROBES.lean.txt'),('SourceCurrentAllocatedNativeSourceIssuedDomainEnterOrigin','EDGE-DOMAIN-PROBES.lean.txt'),('SourceCurrentAllocatedNativeSourceWarmEdgeEntry','WARM-EDGE-ENTRY-PROBES.lean.txt'),('SourceCurrentAllocatedNativeStoredDispatchReturnedWarmEdgeEntry','PROBES.lean.txt')]
laws=[]
for name,probe in specs:
 assert (r/'lean/MicroCFTA'/(name+'.lean')).read_bytes()==(p/(name+'.lean')).read_bytes()
 laws.extend(l.split()[2] for l in (p/probe).read_text().splitlines() if l.startswith('#print axioms '))
assert len(laws)==5
(w/'ResourceProbes.lean.txt').write_bytes((old/'ResourceProbes.lean.txt').read_bytes())
s=(old/'prepare-models-public-generated.py').read_text().replace('20261116-current-source-models-and-warm-admission-publication','20261116-warm-edge-and-recompletion-publication').replace('20261116-source-assignment-checkpoint','20261116-eager-history-invariants-checkpoint').replace("prefix='mcfta-current-models-warm-publication-'","prefix='mcfta-warm-edge-publication-'")
i=s.index('changed=');j=s.index('\nunchanged=',i)
s=s[:i]+"changed={'lean/MicroCFTA/Audit.lean','lean/MicroCFTA/SourceCurrentAllocatedNativeEdgeReturnOrigin.lean','lean/MicroCFTA/SourceCurrentAllocatedNativeEdgeQueryDispatchOrigin.lean','lean/MicroCFTA/SourceCurrentAllocatedNativeSourceIssuedDomainEnterOrigin.lean'}"+s[j:]
lines=s.splitlines(keepends=True)
for i,line in enumerate(lines):
 if line.startswith('modules='):
  modules=ast.literal_eval(line.split('=',1)[1]);lines[i]='modules='+repr(modules+[n for n,_ in specs if n not in modules])+'\n'
 elif line.startswith('laws='):lines[i]='laws='+repr(ast.literal_eval(line.split('=',1)[1])+laws)+'\n'
 elif line.startswith("text='import "):lines[i]='text='+repr(''.join('import MicroCFTA.'+n+'\n' for n,_ in specs))+'\ntext+='+line[len('text='):]
s=''.join(lines)
for a,c in [('assert unchanged==6153','assert unchanged==6161'),('==92','==97'),("'independent_reports':92","'independent_reports':97"),('str(independent),92)','str(independent),97)'),('497','502'),('6165','6167'),('5165','5167'),("'new_public_theorems':13","'new_public_theorems':5"),("'old_non_audit_sources_byte_exact':6153","'old_non_audit_sources_byte_exact':6161"),('ac3fed1766f805c7f355db1bb010d42d32cbf2c6','9f4ad619d01ec5dd187bb6c25db962c60c558da7'),("'MODELS-PUBLIC-API-COMPATIBILITY.json'","'EDGE-PUBLIC-API-COMPATIBILITY.json'")]:
 assert a in s,a;s=s.replace(a,c)
s=s.replace("'actual_warm_entry_and_return_admission_proved':True,","'actual_warm_entry_and_return_admission_proved':True,'actual_warm_node_and_edge_return_admission_proved':True,")
(w/'prepare-public-generated.py').write_text(s);print(json.dumps({'new_modules':2,'owner_exact_prefixes':3,'new_reports':5,'expected_reports':502,'independent_reports':97}))
