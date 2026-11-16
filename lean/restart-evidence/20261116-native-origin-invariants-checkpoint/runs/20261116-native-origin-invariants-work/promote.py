from pathlib import Path
import gzip
import hashlib
import json

root=Path('/home/tritlo/Code/mcfta')
base=root/'lean/restart-evidence'
work=Path(__file__).parent
run=base/'20261116-native-prefix-union-and-next-query-repaired-check'
report=json.loads((run/'checked.json').read_text())
assert len(report['checks'])==3
assert all(c['exit']==0 and not c['nonstandard_axioms'] for c in report['checks'])
sha=lambda data:hashlib.sha256(data).hexdigest()
for name,digest in json.loads((run/'source-pins.json').read_text()).items():
    assert sha((root/name).read_bytes())==digest,name
prior=json.loads(gzip.decompress((base/'20261116-real-worker-original-budget-checkpoint/source-pins.json.gz').read_bytes()))
for name,digest in prior.items():
    assert sha((root/name).read_bytes())==digest,name
audit=root/'lean/MicroCFTA/Audit.lean';old_audit=audit.read_bytes()
assert not (work/'BASE-AUDIT.lean.txt').exists()
(work/'BASE-AUDIT.lean.txt').write_bytes(old_audit)
specs=[
 ('20261116-current-real-selected-prefix-union-normal-ite-names-repair',
  'SourcePruningEnumerationSelectedPrefixUnionNormal.lean',
  '219af06578867a2208bd3dfa7d68f9fca1055bdfab3cf57553921a1f6c6e6d5e'),
 ('20261116-current-past-entry-next-query-domain-open-repair',
  'SourceCurrentAllocatedNativePastEntryNextQueryInnerLaws.lean',
  'ae6c1e7d5a5426e6eafeed7f2617f3590a33caac4db59d61213f4e792fc2731a')]
imports=[];probes=[];files=[]
for folder,name,digest in specs:
    packet=base/folder;raw=(packet/name).read_bytes()
    assert sha(raw)==digest
    target=root/'lean/MicroCFTA'/name;assert not target.exists()
    normalized=raw.rstrip(b'\n')+b'\n'
    assert normalized.rstrip(b'\n')==raw.rstrip(b'\n')
    target.write_bytes(normalized)
    imports.append('import MicroCFTA.'+target.stem+'\n')
    probes.append((packet/'PROBES.lean.txt').read_bytes())
    files.append(target)
audit.write_bytes(''.join(sorted(imports)).encode()+old_audit+b'\n'+b'\n'.join(probes))
assert audit.read_bytes().count(old_audit)==1
assert len(list((root/'lean/MicroCFTA').glob('*.lean')))==6132
result={'prior_checkpoint':'1f61f22734b91de31c05281a205f933cb4773ba8',
    'private_run':run.name,'new_modules':2,'new_public_theorems':2,
    'old_audit_exact_block':True,'other_old_sources_byte_exact':6129,
    'whole_real_worker_resources_unchanged':True,'full_P_retained':True,
    'original_algorithm_budgets_unchanged':True,
    'no_inherited_Returned_or_innerPast_supplier':True,
    'full_worker_union_normal_proved':False,'whole_warm_source_history_proved':False,
    'joint_finite_completion_proved':False,'haskell_changed':False,
    'files':{str(p.relative_to(root)):sha(p.read_bytes()) for p in [audit,*files]}}
(work/'PROMOTION.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))
