from pathlib import Path
import hashlib
import json

root=Path('/home/tritlo/Code/mcfta');base=root/'lean/restart-evidence';work=Path(__file__).parent
run=base/'20261116-terminal-gamma-pending-candidates-check'
checks=json.loads((run/'checks.json').read_text())
specs=[('shared-terminal-union-normal',4,'20261116-current-shared-cached-terminal-union-normal-draft',
 'SourcePruningEnumerationSharedCachedTerminalUnionNormal.lean','8dac689a0bde9625256c1ee4fcfb53cca5d3e42501dd0579d3681dd6c5e5138c'),
 ('stratified-pending-assignment',1,'20261116-current-stratified-pending-assignment-draft',
 'EnumerationPendingAssignment.lean','547ac00c6bb90dcfdd4854a236d0f199721f8e1194d03935e32f9ce328ddc06a')]
sha=lambda data:hashlib.sha256(data).hexdigest()
for name,digest in json.loads((run/'source-pins.json').read_text()).items():assert sha((root/name).read_bytes())==digest,name
imports=[];probes=[];added=[]
for label,count,folder,name,digest in specs:
    report=next(c for c in checks if c['name']==label)
    assert report['exit']==0 and not report['nonstandard_axioms'] and report['total_axiom_reports']==count
    assert 'sorryAx' not in (run/(label+'.txt')).read_text()
    packet=base/folder;raw=(packet/name).read_bytes();assert sha(raw)==digest
    target=root/'lean/MicroCFTA'/name;assert not target.exists();target.write_bytes(raw)
    p=(packet/'PROBES.lean.txt').read_bytes();assert p.count(b'#print axioms ')==count
    imports.append('import MicroCFTA.'+target.stem+'\n');probes.append(p);added.append(target)
audit=root/'lean/MicroCFTA/Audit.lean';old=audit.read_bytes()
(work/'PRE-TERMINAL-AUDIT.lean.txt').write_bytes(old)
audit.write_bytes(''.join(sorted(imports)).encode()+old+b'\n'+b'\n'.join(probes))
assert (work/'BASE-AUDIT.lean.txt').read_bytes() in audit.read_bytes()
result={'independently_passed_modules':2,'independently_passed_new_theorems':5,
 'combined_private_run_passed':False,'failed_warm_candidate_credit':False,
 'new_public_gates_run':False,'joint_finite_completion_proved':False,'haskell_changed':False,
 'files':{str(p.relative_to(root)):sha(p.read_bytes()) for p in [audit,*added]}}
(work/'TERMINAL-ASSIGNMENT-PROMOTION.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))
