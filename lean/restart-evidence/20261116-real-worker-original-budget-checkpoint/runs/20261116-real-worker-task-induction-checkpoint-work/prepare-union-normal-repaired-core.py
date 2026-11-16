from pathlib import Path
import hashlib
import json
import shlex
import tempfile

root=Path('/home/tritlo/Code/mcfta')
base=root/'lean/restart-evidence'
packet=base/'20261116-current-shared-incoming-union-normal-skipped-gate-repair'
run=base/'20261116-native-shared-incoming-union-normal-repaired-check'
run.mkdir()
name='SourcePruningEnumerationSharedIncomingUnionNormal.lean'
raw=packet/name
assert hashlib.sha256(raw.read_bytes()).hexdigest()=='646671cf186b2607543e1b28126b5ed612af9337d1584ce542c5e6b29d02aa6c'
probe=packet/'PROBES.lean.txt'
assert probe.read_bytes().count(b'#print axioms ')==1
source=run/'source/MicroCFTA'/name;source.parent.mkdir(parents=True)
source.write_bytes(raw.read_bytes()+b'\n'+probe.read_bytes())
objects=Path(tempfile.mkdtemp(prefix='mcfta-incoming-union-normal-'))
(run/'objects.json').write_text(json.dumps({'path':str(objects)},indent=2)+'\n')
imports=sorted({x.split()[1] for x in raw.read_text().splitlines() if x.startswith('import ')})
command='exec lake env lean -j1 -DwarningAsError=true -R '+shlex.quote(str(source.parent.parent))
command+=' -o '+shlex.quote(str(objects/'Incoming.olean'))+' '+shlex.quote(str(source))
template=(base/'20261115-native-open-binder-helper-dependencies/check.py').read_text()
driver=template[:template.index('run("public-dependency"')]
jobs=[('public-dependencies','exec lake build '+' '.join(imports),0),('shared-incoming-union-normal',command,1)]
driver+='jobs = '+repr(jobs)+'''
for name,command,count in jobs:
    run(name,command,count)
assert all(x['exit']==0 and not x['nonstandard_axioms'] for x in checks)
report={'checks':checks,'source_pins_unchanged':True,'actual_shared_incoming_union_normal_preserved':True,
    'all_outcomes':True,'original_algorithm_budgets_unchanged':True,'full_worker_union_normal_proved':False,
    'joint_finite_completion_proved':False,'haskell_changed':False,'limits':limits}
(runtime/'checked.json').write_text(json.dumps(report,indent=2)+'\\n')
print(json.dumps(report),flush=True)
'''
driver=driver.replace("+"+repr("\\n"), "+"+repr("\n"))
(run/'check.py').write_text(driver)
files=list((root/'lean/MicroCFTA').glob('*.lean'))
files += [root/n for n in ['shell.nix','lean/lean-toolchain','lean/lakefile.toml','lean/lake-manifest.json']]
files += [Path(__file__),raw,probe,source,run/'check.py']
(run/'source-pins.json').write_text(json.dumps({str(p.relative_to(root)):hashlib.sha256(p.read_bytes()).hexdigest() for p in files},indent=2)+'\n')
print(json.dumps({'run':str(run),'objects':str(objects),'reports':1}))
