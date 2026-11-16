from pathlib import Path
import ast,json
w=Path(__file__).parent;r=w.parents[2];b=w.parent;old=b/'20261116-warm-edge-and-recompletion-work'
specs=[('SourcePruningEnumerationSharedIncomingQueryHistory','20261116-current-prepared-shared-incoming-query-history-draft','PROBES.lean.txt'),('SourcePruningEnumerationOpaqueSuffixIsolation','20261116-current-tuple-finalize-avoidance-assembled','ALIAS-PROBES.lean.txt')]
laws=[]
for name,folder,probe in specs:
 p=b/folder;assert (r/'lean/MicroCFTA'/(name+'.lean')).read_bytes()==(p/(name+'.lean')).read_bytes();laws.extend(l.split()[2] for l in (p/probe).read_text().splitlines() if l.startswith('#print axioms '))
assert len(laws)==2
original=(old/'ResourceProbes.lean.txt').read_bytes();assert original.count(b'#print axioms ')==136
private=(b/'20261116-current-tuple-finalize-avoidance-assembled/PROBES.lean.txt').read_bytes();assert private.count(b'#print axioms ')==1
(w/'OriginalResourceProbes.lean.txt').write_bytes(original);(w/'LocalFinalizeProbe.lean.txt').write_bytes(private);(w/'ResourceProbes.lean.txt').write_bytes(original+b'\n'+private)
s=(old/'prepare-native-path-public-generated.py').read_text().replace('20261116-native-admission-and-parent-path-publication','20261116-incoming-history-and-local-finalize-publication').replace('20261116-eager-history-invariants-checkpoint','20261116-native-path-checkpoint').replace("prefix='mcfta-native-admission-parent-publication-'","prefix='mcfta-incoming-local-finalize-publication-'")
i=s.index('changed=');j=s.index('\nunchanged=',i);s=s[:i]+"changed={'lean/MicroCFTA/Audit.lean','lean/MicroCFTA/SourcePruningEnumerationOpaqueSuffixIsolation.lean','lean/MicroCFTA/SourcePruningEnumerationSharedEagerReservation.lean'}"+s[j:]
lines=s.splitlines(keepends=True)
for i,line in enumerate(lines):
 if line.startswith('modules='):
  modules=ast.literal_eval(line.split('=',1)[1]);lines[i]='modules='+repr(modules+[n for n,_,_ in specs if n not in modules])+'\n'
 elif line.startswith('laws='):lines[i]='laws='+repr(ast.literal_eval(line.split('=',1)[1])+laws)+'\n'
 elif line.startswith("text='import "):lines[i]='text='+repr(''.join('import MicroCFTA.'+n+'\n' for n,_,_ in specs))+'\ntext+='+line[len('text='):]
s=''.join(lines)
for a,c in [('assert unchanged==6160','assert unchanged==6166'),('==102','==104'),("'independent_reports':102","'independent_reports':104"),('str(independent),102)','str(independent),104)'),('507','509'),('6169','6170'),('5169','5170'),("'new_public_theorems':10","'new_public_theorems':2"),("'old_non_audit_sources_byte_exact':6160","'old_non_audit_sources_byte_exact':6166"),('9f4ad619d01ec5dd187bb6c25db962c60c558da7','50fc53f75647f2b141cdddc578e75756e675dccc'),("'NATIVE-PATH-PUBLIC-API-COMPATIBILITY.json'","'INCOMING-FINALIZE-PUBLIC-API-COMPATIBILITY.json'")]:
 assert a in s,a;s=s.replace(a,c)
s=s.replace("==136","==137").replace("str(strict),136)","str(strict),137)").replace("'owner_resource_probes':136","'owner_resource_probes':137,'original_resource_probes':136,'private_local_finalize_probes':1").replace("'owner_resource_probes': 136","'owner_resource_probes': 137,'original_resource_probes':136,'private_local_finalize_probes':1").replace('strict-modules-and-136-resources','strict-modules-136-resources-and-local-proof')
s=s.replace("'actual_prepared_parent_path_congruence_proved':True,","'actual_prepared_parent_path_congruence_proved':True,'actual_prepared_incoming_query_history_proved':True,'private_tuple_finalize_pending_target_avoidance_proved':True,'full_worker_906_avoidance_proved':False,")
(w/'prepare-public-generated.py').write_text(s);print(json.dumps({'source_files':6170,'direct_audit_imports':5170,'reports':509,'independent':104,'original_resource_probes':136,'additional_private_probe':1,'whole906_proved':False}))
