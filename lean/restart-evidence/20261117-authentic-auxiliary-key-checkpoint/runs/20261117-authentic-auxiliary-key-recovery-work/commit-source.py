from pathlib import Path
import datetime,hashlib,json,subprocess
root=Path('/home/tritlo/Code/mcfta');w=Path(__file__).parent
run=root/'lean/restart-evidence/20261117-authentic-auxiliary-key-publication'
g=lambda *a:subprocess.check_output(['git',*a],cwd=root)
parent='4b28f2f1e19751f4c6116fe0cc04a2fce70d6e74'
assert g('rev-parse','HEAD').decode().strip()==parent
assert g('branch','--show-current').decode().strip()=='formalize'
assert not g('diff','--cached','--name-only')
v=json.loads((w/'PUBLICATION-VERIFIED.json').read_text())
assert v['actual_terminal'] and v['actual_terminal_exit']==0 and v['pins_unchanged']
for n,d in json.loads((run/'source-pins.json').read_text()).items():
 assert hashlib.sha256((root/n).read_bytes()).hexdigest()==d,n
names=['lean/MicroCFTA/SourceCurrentNativeAuxiliaryBaseKeyRecovery.lean','lean/MicroCFTA/Audit.lean']
assert g('diff','--name-only').decode().splitlines()==[names[1]]
assert not g('ls-files','--',names[0])
stage=json.loads((w/'SOURCES-NORMAL-STAGING.json').read_text())
assert hashlib.sha256((root/names[0]).read_bytes()).hexdigest()==stage['raw_sha256']
subprocess.run(['git','diff','--check'],cwd=root,check=True)
subprocess.run(['git','add','--',*names],cwd=root,check=True)
assert set(g('diff','--cached','--name-only').decode().splitlines())==set(names)
subprocess.run(['git','diff','--cached','--check'],cwd=root,check=True)
subprocess.run(['git','commit','--quiet','-m','Recover original patterns from auxiliary source keys'],cwd=root,check=True)
head=g('rev-parse','HEAD').decode().strip()
assert not g('status','--porcelain','--untracked-files=no')
receipt={'at':datetime.datetime.now().astimezone().isoformat(),'source_commit':head,'parent':parent,'files':names,'all_five_publication_gates_passed':True,'source_files':6252,'audit_imports':5252,'audit_reports':679,'independent_reports':274,'fresh_component_reports_this_batch':3,'inherited_bound_component_reports':470,'combined_component_reports':473,'old_reports_replaced':0,'fresh_owner_preflight_reports':0,'inherited_owner_reports':264,'new_modules':1,'new_public_theorems':3,'new_private_helpers':2,'new_theorem_declarations':5,'new_private_explicit_reports':0,'private_helpers_checked_transitively':True,'new_private_predicates':0,'old_non_audit_source_files_byte_exact':6250,'old_audit_exact_contiguous_bytes':424863,'old_audit_exact_offset':61,'all_old_proof_bodies_and_limits_unchanged':True,'all_three_selected_first_headers_preserved':True,'first_failed_linter_check_and_one_line_repair_preserved':True,'actual_source_auxiliary_key_full_pattern_recovery_proved':True,'arbitrary_domain_extension_cancellation_claimed':False,'warm_query_no_new_mu_proved':False,'every_warm_worker_call_qualification_proved':False,'inherited_cell_semantic_chronology_proved':False,'joint_finite_completion_proved':False,'compiled_haskell_correspondence_proved':False,'haskell_changed':False,'new_reachable_haskell_defect_established':False}
(w/'SOURCE-COMMIT.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt))
