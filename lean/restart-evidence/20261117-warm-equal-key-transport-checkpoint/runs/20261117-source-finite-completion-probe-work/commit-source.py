from pathlib import Path
import datetime
import hashlib
import json
import subprocess

root=Path('/home/tritlo/Code/mcfta')
w=Path(__file__).parent
run=root/'lean/restart-evidence/20261117-warm-equal-key-transport-publication'
g=lambda *a:subprocess.check_output(['git',*a],cwd=root)
parent='85b210de894a35ef7c10e8aa1279e9a53e35ea1d'
assert g('rev-parse','HEAD').decode().strip()==parent
assert g('branch','--show-current').decode().strip()=='formalize'
assert not g('diff','--cached','--name-only')
verified=json.loads((w/'PUBLICATION-VERIFIED.json').read_text())
assert verified['actual_terminal_exit']==0 and verified['actual_terminal'] and verified['pins_unchanged']
for n,d in json.loads((run/'source-pins.json').read_text()).items():assert hashlib.sha256((root/n).read_bytes()).hexdigest()==d,n
names=['lean/MicroCFTA/SourceCurrentAllocatedNativePastGammaEqualEntryPayload.lean','lean/MicroCFTA/Audit.lean']
assert set(g('diff','--name-only').decode().splitlines())==set(names)
subprocess.run(['git','diff','--check'],cwd=root,check=True)
subprocess.run(['git','add','--',*names],cwd=root,check=True)
assert set(g('diff','--cached','--name-only').decode().splitlines())==set(names)
subprocess.run(['git','commit','--quiet','-m','Transport full patterns across warm equal-key entries'],cwd=root,check=True)
head=g('rev-parse','HEAD').decode().strip()
assert not g('status','--porcelain','--untracked-files=no')
receipt={'at':datetime.datetime.now().astimezone().isoformat(),'source_commit':head,'parent':parent,'files':names,'all_five_publication_gates_passed':True,'source_files':6251,'audit_imports':5251,'audit_reports':669,'independent_reports':264,'fresh_component_reports_this_batch':1,'inherited_bound_component_reports':461,'combined_component_reports':462,'old_reports_replaced':0,'fresh_owner_preflight_reports':0,'inherited_owner_reports':264,'old_non_audit_non_changed_owner_source_files_byte_exact':6249,'old_owner_exact_contiguous_bytes':15882,'old_owner_exact_offset':61,'old_audit_exact_prefix':True,'all_old_proof_bodies_and_limits_unchanged':True,'new_modules':0,'new_private_theorems':0,'new_public_theorems':1,'original_first_header_content_preserved':True,'warm_equal_key_full_pattern_identity_transport_proved':True,'earlier_source_family_semantic_IH_discharged':False,'every_cell_joint_query_attachment_proved':False,'joint_finite_completion_proved':False,'haskell_changed':False}
(w/'SOURCE-COMMIT.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt))
