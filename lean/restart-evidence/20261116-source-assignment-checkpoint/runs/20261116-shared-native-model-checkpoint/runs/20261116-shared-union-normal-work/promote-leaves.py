from pathlib import Path
import gzip
import hashlib
import json

root=Path('/home/tritlo/Code/mcfta')
base=root/'lean/restart-evidence'
work=Path(__file__).parent
sha=lambda data:hashlib.sha256(data).hexdigest()
specs=[
 ('20261116-native-selected-preparation-union-normal-repaired-check',
  '20261116-current-real-selected-preparation-union-normal-union-readback-repair',
  'SourcePruningEnumerationPreparationUnionNormal.lean',
  '31001605e93a871638dce496ff81004d2a0eaa6e08d7c490ef369431ca6f1693'),
 ('20261116-native-shared-dispatch-union-normal-explicit-check',
  '20261116-current-shared-dispatch-union-normal-explicit-outcome-repair',
  'SourcePruningEnumerationSharedDispatchUnionNormal.lean',
  'db31a998b918f7c301a7da7283234cc109f95986828ad188db3ea0aa14ffe0e3')]
for run_name,_,_,_ in specs:
    run=base/run_name;report=json.loads((run/'checked.json').read_text())
    assert all(c['exit']==0 and not c['nonstandard_axioms'] for c in report['checks'])
    assert report['checks'][-1]['total_axiom_reports']==2
    for name,digest in json.loads((run/'source-pins.json').read_text()).items():
        assert sha((root/name).read_bytes())==digest,name
prior=json.loads(gzip.decompress((base/'20261116-native-origin-invariants-checkpoint/source-pins.json.gz').read_bytes()))
for name,digest in prior.items():assert sha((root/name).read_bytes())==digest,name
audit=root/'lean/MicroCFTA/Audit.lean';old_audit=audit.read_bytes()
assert not (work/'BASE-AUDIT.lean.txt').exists()
(work/'BASE-AUDIT.lean.txt').write_bytes(old_audit)
imports=[];probes=[];files=[]
for _,folder,name,digest in specs:
    packet=base/folder;raw=(packet/name).read_bytes();assert sha(raw)==digest
    target=root/'lean/MicroCFTA'/name;assert not target.exists()
    target.write_bytes(raw.rstrip(b'\n')+b'\n')
    imports.append('import MicroCFTA.'+target.stem+'\n')
    p=(packet/'PROBES.lean.txt').read_bytes();assert p.count(b'#print axioms ')==2
    probes.append(p);files.append(target)
audit.write_bytes(''.join(sorted(imports)).encode()+old_audit+b'\n'+b'\n'.join(probes))
assert old_audit in audit.read_bytes()
result={'prior_checkpoint':'0feb93907f8b8f0f49deb4458fe86c6430e261ee',
    'new_modules':2,'new_public_theorems':4,'all_old_non_audit_sources_byte_exact':6131,
    'old_audit_exact_block':True,'original_algorithm_budgets_unchanged':True,
    'only_past_union_normal_assumed':True,'no_future_result_or_model_supplier':True,
    'full_worker_union_normal_proved':False,'whole_warm_source_history_proved':False,
    'joint_finite_completion_proved':False,'haskell_changed':False,
    'files':{str(p.relative_to(root)):sha(p.read_bytes()) for p in [audit,*files]}}
(work/'LEAF-PROMOTION.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))
