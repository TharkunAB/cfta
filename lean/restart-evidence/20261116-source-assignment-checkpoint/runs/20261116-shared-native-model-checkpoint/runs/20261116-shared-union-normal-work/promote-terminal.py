from pathlib import Path
import hashlib
import json

root=Path('/home/tritlo/Code/mcfta');base=root/'lean/restart-evidence';work=Path(__file__).parent
run=base/'20261116-terminal-gamma-pending-candidates-check'
sha=lambda data:hashlib.sha256(data).hexdigest()
for name,digest in json.loads((run/'source-pins.json').read_text()).items():assert sha((root/name).read_bytes())==digest,name
report=next(c for c in json.loads((run/'checks.json').read_text()) if c['name']=='shared-terminal-union-normal')
assert report['exit']==0 and report['total_axiom_reports']==4 and not report['nonstandard_axioms']
assert 'sorryAx' not in (run/'shared-terminal-union-normal.txt').read_text()
packet=base/'20261116-current-shared-cached-terminal-union-normal-draft'
name='SourcePruningEnumerationSharedCachedTerminalUnionNormal.lean'
raw=(packet/name).read_bytes();assert sha(raw)=='8dac689a0bde9625256c1ee4fcfb53cca5d3e42501dd0579d3681dd6c5e5138c'
target=root/'lean/MicroCFTA'/name;assert target.read_bytes()==raw
probes=(packet/'PROBES.lean.txt').read_bytes();assert probes.count(b'#print axioms ')==4
audit=root/'lean/MicroCFTA/Audit.lean';old=audit.read_bytes()
assert ('import MicroCFTA.'+target.stem).encode() not in old
(work/'PRE-TERMINAL-AUDIT.lean.txt').write_bytes(old)
audit.write_bytes(('import MicroCFTA.'+target.stem+'\n').encode()+old+b'\n'+probes)
assert (work/'BASE-AUDIT.lean.txt').read_bytes() in audit.read_bytes()
(work/'TERMINAL-PROMOTION.json').write_text(json.dumps({'private_terminal_passed':True,
 'old_pending_assignment_source_preserved':True,'duplicate_assignment_candidate_not_promoted':True,
 'public_five_gates_run':False,'joint_finite_completion_proved':False,'haskell_changed':False,
 'audit':sha(audit.read_bytes()),'module':sha(raw)},indent=2)+'\n')
print('Terminal source and four Audit probes added; existing pending assignment engine preserved.')
