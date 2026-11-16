from pathlib import Path
import hashlib
import json
import subprocess

root=Path('/home/tritlo/Code/mcfta')
base=root/'lean/restart-evidence'
work=Path(__file__).parent
owner=root/'lean/MicroCFTA/SourcePruningEnumerationSharedEagerReservation.lean'
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip()=='527ee252bf74cd980979727e7439a7cc1e97b9bc'
assert not subprocess.check_output(['git','status','--porcelain','--untracked-files=no'],cwd=root,text=True)
run=base/'20261116-native-real-task-and-opaque-subset-check'
checks=json.loads((run/'checks.json').read_text())
assert all(x['exit']==0 and not x['nonstandard_axioms'] for x in checks)
pins=json.loads((run/'source-pins.json').read_text())
components=[
 (base/'20261116-current-real-actual-source-rows-plan-and-helper-repair/APPEND.lean.txt','Derive actual real row inputs and resource induction'),
 (work/'CORE-FIRST-FIVE.lean.txt','Prove real task resource induction and captured startup'),
 (base/'20261116-current-real-opaque-prepared-typing-repair/OPAQUE-APPEND.lean.txt','Prove actual opaque outcomes retain resources')]
commits=[]
for p,message in components:
    data=p.read_bytes();assert hashlib.sha256(data).hexdigest()==pins[str(p.relative_to(root))]
    before=owner.read_bytes();owner.write_bytes(before+b'\n'+data)
    assert owner.read_bytes().startswith(before)
    subprocess.run(['git','diff','--check'],cwd=root,check=True)
    subprocess.run(['git','add',str(owner.relative_to(root))],cwd=root,check=True)
    subprocess.run(['git','commit','--quiet','-m',message],cwd=root,check=True)
    commits.append(subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip())
(work/'SUBSET-PROMOTION.json').write_text(json.dumps({'commits':commits,'checked_private_session':45622,
    'owner_probes':123,'standard_reports':121,'axiom_free_reports':2,
    'genuine_task_induction_discharged':True,'smaller_depth_worker_ih_still_required':True,
    'full_real_worker_proved':False,'joint_finite_completion_proved':False,'haskell_changed':False},indent=2)+'\n')
print(json.dumps({'commits':commits,'head':commits[-1]}))
