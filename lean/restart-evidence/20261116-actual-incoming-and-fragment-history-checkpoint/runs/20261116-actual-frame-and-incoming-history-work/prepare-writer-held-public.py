from pathlib import Path
import ast,json
w=Path(__file__).parent;r=w.parents[2];b=w.parent
proofs=[('20261116-current-held-fragment-history-owner-assembly','PROBES.lean.txt'),('20261116-current-held-fragment-history-projection-owner-assembly','PROBES.lean.txt'),('20261116-current-prepared-shared-incoming-writer-history-projection-repair','PROBES.lean.txt')]
laws=[]
for folder,name in proofs:laws.extend(s.split()[2] for s in (b/folder/name).read_text().splitlines() if s.startswith('#print axioms '))
assert len(laws)==5
resources=(w/'OriginalResourceProbes.lean.txt').read_bytes();assert resources.count(b'#print axioms ')==136
private_packets=['20261116-current-tuple-finalize-avoidance-assembled','20261116-current-tuple-finalize-held-history-assembled','20261116-current-captured-tuple-before-pending-doc-comment-repair','20261116-current-ordinary-capture-isolated-boundary-separation-draft','20261116-current-real-callback-held-fragment-history-draft']
for folder in private_packets:resources+=b'\n'+(b/folder/'PROBES.lean.txt').read_bytes()
assert resources.count(b'#print axioms ')==143
(w/'ResourceProbesWithHeldHistory.lean.txt').write_bytes(resources)
s=(w/'prepare-public-generated.py').read_text().replace('20261116-incoming-history-and-local-finalize-publication','20261116-writer-and-held-fragment-history-publication').replace("prefix='mcfta-incoming-local-finalize-publication-'","prefix='mcfta-writer-held-fragment-publication-'").replace('ResourceProbes.lean.txt','ResourceProbesWithHeldHistory.lean.txt')
lines=s.splitlines(keepends=True)
for i,line in enumerate(lines):
 if line.startswith('modules='):
  modules=ast.literal_eval(line.split('=',1)[1]);n='SourcePruningEnumerationSharedIncomingWriterHistory';lines[i]='modules='+repr(modules+[n] if n not in modules else modules)+'\n'
 elif line.startswith('laws='):lines[i]='laws='+repr(ast.literal_eval(line.split('=',1)[1])+laws)+'\n'
 elif line.startswith("text='import "):lines[i]="text='import MicroCFTA.SourcePruningEnumerationSharedIncomingWriterHistory\\n'\ntext+="+line[len('text='):]
s=''.join(lines)
for a,c in [('==104','==109'),("'independent_reports':104","'independent_reports':109"),('str(independent),104)','str(independent),109)'),('509','514'),('6170','6171'),('5170','5171'),("'new_public_theorems':2","'new_public_theorems':7"),('==137','==143'),('str(strict),137)','str(strict),143)'),("'owner_resource_probes':137","'owner_resource_probes':143"),("'owner_reports':136","'owner_reports':143"),('strict-modules-136-resources-and-local-proof','strict-modules-136-resources-and-held-history'),('INCOMING-FINALIZE-PUBLIC-API-COMPATIBILITY.json','WRITER-HELD-HISTORY-PUBLIC-API-COMPATIBILITY.json')]:
 assert a in s,a;s=s.replace(a,c)
s=s.replace("'private_local_finalize_probes':1","'private_local_finalize_probes':2,'private_source_qualification_and_callback_probes':5,'total_private_resource_probes':7")
s=s.replace("'full_worker_906_avoidance_proved':False,","'full_worker_906_avoidance_proved':False,'past_to_actual_performed_phase_history_proved':True,'concrete_held_fragment_receipt_composition_proved':True,'concrete_held_fragment_pending_target_projection_proved':True,'private_tuple_finalize_held_history_proved':True,'private_actual_captured_pending_at_rowOwn_proved':True,'private_captured_boundary_separation_proved':True,'private_actual_callback_held_history_with_genuine_depth_IH_proved':True,")
(w/'prepare-writer-held-public-generated.py').write_text(s);print(json.dumps(dict(source_files=6171,direct_imports=5171,public_reports=514,independent_reports=109,resource_reports=143,original_resource_probes=136,private_probes=7,whole906=False)))
