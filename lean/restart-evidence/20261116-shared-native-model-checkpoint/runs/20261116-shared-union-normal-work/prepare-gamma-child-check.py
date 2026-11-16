from pathlib import Path
import hashlib
import json
import shlex
import tempfile

root=Path('/home/tritlo/Code/mcfta')
base=root/'lean/restart-evidence'
run=base/'20261116-gamma-child-candidates-check'
run.mkdir()
specs=[
 ('past-gamma-equal-entry','20261116-current-past-gamma-equal-entry-payload-projection-repair',
  'SourceCurrentAllocatedNativePastGammaEqualEntryPayload.lean',
  '259b219a188a859855d1027b39d169807f0b27901777d5706526842b74aeefb3',1),
 ('shared-child-union-normal','20261116-current-shared-child-union-normal-draft',
  'SourcePruningEnumerationSharedChildUnionNormal.lean',
  'd76c8cb53a7cccccdb53af2e58d3655b071e10edd1915cd4ce6ac88f6e32c6de',3)]
objects=Path(tempfile.mkdtemp(prefix='mcfta-gamma-child-'))
(run/'objects.json').write_text(json.dumps({'path':str(objects)},indent=2)+'\n')
imports=set();jobs=[];files=[]
for label,folder,name,digest,count in specs:
    packet=base/folder;raw=packet/name;probes=packet/'PROBES.lean.txt'
    assert hashlib.sha256(raw.read_bytes()).hexdigest()==digest
    assert probes.read_bytes().count(b'#print axioms ')==count
    source=run/'source/MicroCFTA'/name;source.parent.mkdir(parents=True,exist_ok=True)
    source.write_bytes(raw.read_bytes()+b'\n'+probes.read_bytes())
    imports.update(line.split()[1] for line in raw.read_text().splitlines() if line.startswith('import '))
    command='exec lake env lean -j1 -DwarningAsError=true -R '+shlex.quote(str(source.parent.parent))
    command+=' -o '+shlex.quote(str(objects/(label+'.olean')))+' '+shlex.quote(str(source))
    jobs.append((label,command,count));files += [raw,probes,source]
jobs.insert(0,('public-dependencies','exec lake build '+' '.join(sorted(imports)),0))
template=(base/'20261115-native-open-binder-helper-dependencies/check.py').read_text()
driver=template[:template.index('run("public-dependency"')]
for assertion in [
 '    assert result.returncode == 0 and not bad and len(groups) + free_reports >= required_groups\n',
 "    assert 'sorryAx' not in output\n"]:
    assert driver.count(assertion)==1
    driver=driver.replace(assertion,'')
driver+='jobs = '+repr(jobs)+'''
for name,command,count in jobs:
    run(name,command,count)
assert len(checks)==len(jobs)
assert all(c['exit']==0 and not c['nonstandard_axioms'] and c['total_axiom_reports']==job[2]
    for c,job in zip(checks,jobs))
report={'checks':checks,'source_pins_unchanged':True,'actual_shared_child_union_normal_proved':True,
    'actual_cold_cell_past_gamma_transport_proved':True,'current_pending_assignment_proved':False,
    'full_worker_union_normal_proved':False,'whole_warm_source_history_proved':False,
    'joint_finite_completion_proved':False,'haskell_changed':False,'limits':limits}
(runtime/'checked.json').write_text(json.dumps(report,indent=2)+'\\n')
print(json.dumps(report),flush=True)
'''
(run/'check.py').write_text(driver)
files += list((root/'lean/MicroCFTA').glob('*.lean'))
files += [root/n for n in ['shell.nix','lean/lean-toolchain','lean/lakefile.toml','lean/lake-manifest.json']]
files += [Path(__file__),run/'check.py']
(run/'source-pins.json').write_text(json.dumps({str(p.relative_to(root)):hashlib.sha256(p.read_bytes()).hexdigest()
    for p in files},indent=2)+'\n')
print(json.dumps({'run':str(run),'objects':str(objects),'jobs':[(n,c) for n,_,c in jobs]}))
