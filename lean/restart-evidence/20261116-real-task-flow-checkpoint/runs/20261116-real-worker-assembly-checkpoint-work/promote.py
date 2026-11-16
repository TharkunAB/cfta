from pathlib import Path
import datetime
import hashlib
import json
import subprocess

root=Path('/home/tritlo/Code/mcfta')
base=root/'lean/restart-evidence'
work=Path(__file__).parent
read=lambda *args:subprocess.check_output(['git',*args],cwd=root,text=True).strip()
assert read('rev-parse','HEAD')=='21b36cd26e9841ca63b09bda62432057da1ad9ad'
assert read('branch','--show-current')=='formalize' and not read('diff','--cached','--name-only')
assert read('diff','--name-only')=='lean/MicroCFTA/SourcePruningEnumerationObservedRealPrefixResources.lean'
run=base/'20261116-native-real-runtime-and-prefix-admission-check'
checks=json.loads((run/'checks.json').read_text())
for name,count in [('public-receipt-imports',3),('0-20261116-real-worker-assembly-checkpoint-work',89)]:
    item=next(x for x in checks if x['name']==name)
    assert item['exit']==0 and item['total_axiom_reports']==count and not item['nonstandard_axioms']
for name,digest in json.loads((run/'source-pins.json').read_text()).items():
    assert hashlib.sha256((root/name).read_bytes()).hexdigest()==digest,name
admission_run=base/'20261116-native-real-prefix-admission-le-trans-check'
assert all(x['exit']==0 and not x['nonstandard_axioms'] for x in json.loads((admission_run/'checked.json').read_text())['checks'])
for name,digest in json.loads((admission_run/'source-pins.json').read_text()).items():
    assert hashlib.sha256((root/name).read_bytes()).hexdigest()==digest,name
nullary_run=base/'20261116-native-real-task-runtime-and-nullary-check'
item=next(x for x in json.loads((nullary_run/'checks.json').read_text()) if x['name']=='real-nullary-pattern')
assert item['exit']==0 and item['total_axiom_reports']==1 and not item['nonstandard_axioms']
audit=root/'lean/MicroCFTA/Audit.lean'
owner=root/'lean/MicroCFTA/SourcePruningEnumerationSharedEagerReservation.lean'
(work/'BASE-AUDIT.lean.txt').write_bytes(audit.read_bytes())
(work/'BASE-OWNER.lean.txt').write_bytes(owner.read_bytes())
commits=[]
def commit(message,paths):
    subprocess.run(['git','add','--',*paths],cwd=root,check=True)
    subprocess.run(['git','diff','--cached','--check'],cwd=root,check=True)
    subprocess.run(['git','commit','--quiet','-m',message],cwd=root,check=True)
    commits.append(read('rev-parse','HEAD'))
probes=''
for name in ['observed_success_stages','prepared_done_narrowed','prepared_success_nonempty']:
    q='MicroCFTA.SourcePruningEnumerationSharedRecursive.'+name
    probes+='\n#check @'+q+'\n#print axioms '+q+'\n'
audit.write_bytes(audit.read_bytes()+probes.encode())
commit('Expose actual real-prefix receipts for cross-module proofs',
    ['lean/MicroCFTA/SourcePruningEnumerationObservedRealPrefixResources.lean','lean/MicroCFTA/Audit.lean'])
raw=base/'20261116-current-real-actual-task-runtime-root-width-repair/APPEND.lean.txt'
assert hashlib.sha256(raw.read_bytes()).hexdigest()=='88f833fdc606da369f450a2b207354f15bd92f03927d0af9a6936681e13c0364'
owner.write_bytes(owner.read_bytes()+b'\n'+raw.read_bytes())
commit('Reuse source task data for generic real worker runtime', [str(owner.relative_to(root))])
specs=[
 ('20261116-current-real-nullary-captured-frame-pattern-repair',
  'SourcePruningEnumerationRealNullaryCapturedFrameResources.lean',
  'a5e1fecbd88feddd98deef2a3344698d50ae0b4940f1b5d33d45ffd8ea6b996d',
  'MicroCFTA.SourcePruningEnumerationRealNullaryCapturedFrameResources.nullary_captured_frame_resources_at_original_budget',
  'Prove actual nullary captured-row resources at the original budget'),
 ('20261116-current-real-prefix-admission-le-trans-repair',
  'SourcePruningEnumerationObservedRealPrefixAdmission.lean',
  '404a6327d9c6a51db3fe2713ea69ef18864b710344cad32ad9d7c370a95f37e3',
  'MicroCFTA.SourcePruningEnumerationSharedRecursive.prefix_real_phase_admission_at_original_budget',
  'Derive actual real-prefix admission at the supplied budget'),
]
for folder,name,digest,q,message in specs:
    raw=base/folder/name
    assert hashlib.sha256(raw.read_bytes()).hexdigest()==digest
    target=root/'lean/MicroCFTA'/name
    assert not target.exists()
    target.write_bytes(raw.read_bytes())
    audit.write_bytes(('import MicroCFTA.'+target.stem+'\n').encode()+audit.read_bytes()+('\n#check @'+q+'\n#print axioms '+q+'\n').encode())
    commit(message,[str(target.relative_to(root)),'lean/MicroCFTA/Audit.lean'])
(work/'promotion.json').write_text(json.dumps({'at':datetime.datetime.now().astimezone().isoformat(),
    'base':'21b36cd26e9841ca63b09bda62432057da1ad9ad','commits':commits,'code':read('rev-parse','HEAD'),
    'source_files':6128,'new_public_theorems':2,'existing_exact_receipt_exports':3,
    'generic_runtime_equations_proved':8,'whole_real_worker_proved':False,
    'joint_finite_completion_proved':False,'haskell_changed':False},indent=2)+'\n')
print(json.dumps({'code':read('rev-parse','HEAD'),'commits':commits}))
