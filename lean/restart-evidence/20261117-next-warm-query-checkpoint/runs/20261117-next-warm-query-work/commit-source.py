from pathlib import Path
import datetime,hashlib,json,subprocess
root=Path('/home/tritlo/Code/mcfta'); w=Path(__file__).parent
run=root/'lean/restart-evidence/20261117-next-warm-query-publication'
g=lambda *a:subprocess.check_output(['git',*a],cwd=root)
parent='5535b223b6f3de67706096a9eab337e160faae47'
assert g('rev-parse','HEAD').decode().strip()==parent
assert g('branch','--show-current').decode().strip()=='formalize'
assert not g('diff','--cached','--name-only')
v=json.loads((w/'PUBLICATION-VERIFIED.json').read_text())
assert v['actual_terminal_exit']==0 and v['actual_terminal'] and v['pins_unchanged']
for n,d in json.loads((run/'source-pins.json').read_text()).items():
 assert hashlib.sha256((root/n).read_bytes()).hexdigest()==d,n
names=['lean/MicroCFTA/SourceSynthesisCurrentUniverseNativeAllocation.lean','lean/MicroCFTA/SourceCurrentAllocatedNativePastGammaEqualEntryPayload.lean','lean/MicroCFTA/Audit.lean']
assert set(g('diff','--name-only').decode().splitlines())==set(names)
subprocess.run(['git','diff','--check'],cwd=root,check=True)
subprocess.run(['git','add','--',*names],cwd=root,check=True)
assert set(g('diff','--cached','--name-only').decode().splitlines())==set(names)
subprocess.run(['git','commit','--quiet','-m','Recover source admission for returned native cache cells'],cwd=root,check=True)
head=g('rev-parse','HEAD').decode().strip()
assert not g('status','--porcelain','--untracked-files=no')
receipt={'at':datetime.datetime.now().astimezone().isoformat(),'source_commit':head,'parent':parent,'files':names,'all_five_publication_gates_passed':True,'source_files':6251,'audit_imports':5251,'audit_reports':676,'independent_reports':271,'fresh_component_reports_this_batch':8,'inherited_bound_component_reports':462,'combined_component_reports':470,'old_reports_replaced':0,'fresh_owner_preflight_reports':0,'inherited_owner_reports':264,'old_non_audit_non_changed_owner_source_files_byte_exact':6248,'old_native_exact_contiguous_bytes':169023,'old_native_exact_offset':62,'old_gamma_exact_prefix_bytes':26430,'old_audit_exact_prefix':True,'all_old_proof_bodies_and_limits_unchanged':True,'new_modules':0,'new_private_theorems':1,'new_public_theorems':7,'new_private_predicates':0,'all_selected_first_header_content_preserved':True,'generic_closed_root_returned_node_entry_proved':True,'cold_returned_node_Profile_without_supplied_old_entry_proved':True,'all_old_edge_children_requalified_jointly_proved':True,'full_prefix_source_admission_with_past_inventory_proved':True,'all_old_cold_returned_node_and_edge_full_admission_proved':True,'input_pair_qualifications_still_explicit':True,'every_warm_worker_call_qualification_proved':False,'warm_query_no_new_mu_proved':False,'all_warm_cells_source_qualification_proved':False,'joint_finite_completion_proved':False,'compiled_haskell_correspondence_proved':False,'haskell_changed':False,'new_reachable_haskell_defect_established':False}
(w/'SOURCE-COMMIT.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt))
