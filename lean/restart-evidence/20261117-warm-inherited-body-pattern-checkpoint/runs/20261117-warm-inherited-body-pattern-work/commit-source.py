from pathlib import Path
import datetime,hashlib,json,subprocess
root=Path('/home/tritlo/Code/mcfta');w=Path(__file__).parent
run=root/'lean/restart-evidence/20261117-warm-inherited-body-pattern-publication'
g=lambda *a:subprocess.check_output(['git',*a],cwd=root)
parent='936d0a600d831e3ab1bca29fdd3464ccebef101a'
assert g('rev-parse','HEAD').decode().strip()==parent
assert g('branch','--show-current').decode().strip()=='formalize'
assert not g('diff','--cached','--name-only')
v=json.loads((w/'PUBLICATION-VERIFIED.json').read_text())
assert v['actual_terminal'] and v['actual_terminal_exit']==0 and v['pins_unchanged']
for n,d in json.loads((run/'source-pins.json').read_text()).items():
 assert hashlib.sha256((root/n).read_bytes()).hexdigest()==d,n
names=['lean/MicroCFTA/SourceSynthesisCurrentUniverseWarmInheritedChild.lean','lean/MicroCFTA/Audit.lean']
assert g('diff','--name-only').decode().splitlines()==[names[1]]
assert not g('ls-files','--',names[0])
stage=json.loads((w/'SOURCES-NORMAL-STAGING.json').read_text())
assert hashlib.sha256((root/names[0]).read_bytes()).hexdigest()==stage['raw_sha256']
subprocess.run(['git','diff','--check'],cwd=root,check=True)
subprocess.run(['git','add','--',*names],cwd=root,check=True)
assert set(g('diff','--cached','--name-only').decode().splitlines())==set(names)
subprocess.run(['git','diff','--cached','--check'],cwd=root,check=True)
subprocess.run(['git','commit','--quiet','-m','Derive binder-pair absence for inherited B/P cache hits'],cwd=root,check=True)
head=g('rev-parse','HEAD').decode().strip()
assert not g('status','--porcelain','--untracked-files=no')
receipt={'at':datetime.datetime.now().astimezone().isoformat(),'source_commit':head,'parent':parent,'files':names,'all_five_publication_gates_passed':True,'source_files':6253,'audit_imports':5253,'audit_reports':680,'independent_reports':275,'fresh_component_reports_this_batch':1,'inherited_bound_component_reports':473,'combined_component_reports':474,'old_reports_replaced':0,'fresh_owner_preflight_reports':0,'inherited_owner_reports':264,'new_modules':1,'new_public_theorems':1,'new_private_helpers':0,'new_theorem_declarations':1,'new_private_explicit_reports':0,'new_private_predicates':0,'old_non_audit_source_files_byte_exact':6251,'old_audit_exact_contiguous_bytes':425558,'old_audit_exact_offset':66,'all_old_proof_bodies_and_limits_unchanged':True,'both_selected_first_headers_preserved':True,'full_open_header_not_compiled':True,'first_check_passed_without_repair':True,'actual_inherited_cold_BP_hit_pair_absence_proved':True,'qualification_derived_internally':True,'fresh_evaluated_child_pair_absence_proved':False,'same_warm_produced_cells_pair_absence_proved':False,'warm_query_no_new_mu_proved':False,'every_warm_worker_call_qualification_proved':False,'joint_finite_completion_proved':False,'compiled_haskell_correspondence_proved':False,'haskell_changed':False,'new_reachable_haskell_defect_established':False}
(w/'SOURCE-COMMIT.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt))
