from pathlib import Path
import gzip
import hashlib
import json
import tempfile

root=Path('/home/tritlo/Code/mcfta')
work=Path(__file__).parent
runtime=root/'lean/restart-evidence/20261115-real-prefix-and-opaque-publication'
runtime.mkdir()
owner=root/'lean/MicroCFTA/SourcePruningEnumerationSharedEagerReservation.lean'
real=root/'lean/MicroCFTA/SourcePruningEnumerationObservedRealPrefixResources.lean'
promotion=json.loads((work/'promotion.json').read_text())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
prior=root/'lean/restart-evidence/20261115-actual-source-task-scan-checkpoint'
pins_old=json.loads(gzip.decompress((prior/'source-pins.json.gz').read_bytes()))
changed={str(owner.relative_to(root)),'lean/MicroCFTA/Audit.lean'}
unchanged=0
for name,digest in pins_old.items():
    if name not in changed:
        assert sha(root/name)==digest,name
        if name.startswith('lean/MicroCFTA/'):unchanged+=1
assert unchanged==6117
old=root/'lean/restart-evidence/20261115-current-actual-prepared-scan-final-opacity-resource-bundle/PROBES.lean.txt'
opaque=root/'lean/restart-evidence/20261115-current-actual-source-opaque-terminal-scrutinee-repair/PROBES.lean.txt'
probe=old.read_bytes()+b'\n'+opaque.read_bytes()
assert probe.count(b'#print axioms ')==73
(runtime/'ResourceProbes.lean.txt').write_bytes(probe)
sroot=runtime/'source';source=sroot/'MicroCFTA'/owner.name;source.parent.mkdir(parents=True)
source.write_bytes(owner.read_bytes()+b'\n'+probe)
objects=Path(tempfile.mkdtemp(prefix='mcfta-real-prefix-publication-'))
(runtime/'objects.json').write_text(json.dumps({'path':str(objects)},indent=2)+'\n')
strict=runtime/'strict-modules.py'
strict.write_text('''import os,subprocess
commands = '''+repr([['lake','env','lean','-j1','-DwarningAsError=true','-R',str(sroot),'-o',str(objects/'Owner.olean'),str(source)],['lake','env','lean','-j1','-DwarningAsError=true','-o',str(objects/'Real.olean'),str(real)]])+'''\nfor command in commands:
    subprocess.run(command,check=True)
''')
independent=runtime/'IndependentProbes.lean'
previous=root/'lean/restart-evidence/20261115-actual-source-task-scan-publication/IndependentProbes.lean'
independent.write_text(previous.read_text().replace('import MicroCFTA.SourcePruningEnumerationSharedEagerReservation','import MicroCFTA.SourcePruningEnumerationObservedRealPrefixResources\nimport MicroCFTA.SourcePruningEnumerationSharedEagerReservation',1)+'\n#check @MicroCFTA.SourcePruningEnumerationSharedRecursive.prefix_real_narrowed_resources_at_original_budget\n#print axioms MicroCFTA.SourcePruningEnumerationSharedRecursive.prefix_real_narrowed_resources_at_original_budget\n')
template=(root/'lean/restart-evidence/20261115-native-open-binder-helper-dependencies/check.py').read_text()
driver=template[:template.index('run("public-dependency"')]
jobs=[('public-build','exec lake build',0),('strict-modules-and-73-resources','exec python3 '+str(strict),73),('independent-imports','exec lake env lean -j1 -DwarningAsError=true '+str(independent),4),('audit-build','exec lake build MicroCFTA.Audit',0),('audit-strict','exec lake env lean -j1 -DwarningAsError=true MicroCFTA/Audit.lean',409)]
driver+='jobs = '+repr(jobs)+'\n'
driver+='''for name,command,count in jobs:
    run(name,command,count)
match=re.search(r'Checked axiom dependencies of (\\d+) MicroCFTA theorems\\.',(runtime/'audit-strict.txt').read_text())
assert match and checks[-1]['total_axiom_reports']==409
report={'checks':checks,'source_pins_unchanged':True,'audited_theorems':int(match.group(1)),
    'individual_reports':409,'retained_resource_probes':66,'new_resource_probes_since_native_checkpoint':7,
    'actual_opaque_terminal_resources_at_original_budget_proved':True,
    'actual_successful_real_narrowed_right_prefix_resources_at_original_budget_proved':True,
    'real_prefix_scope':'Successful nonempty narrowed-Right prefix; original action and exact endpoint retained.',
    'whole_identity_worker_at_any_budget_proved':False,'whole_real_worker_at_any_budget_proved':False,
    'joint_finite_completion_proved':False,'compiled_haskell_correspondence_proved':False,
    'haskell_changed':False,'at':datetime.datetime.now().astimezone().isoformat(),'limits':limits}
(runtime/'checked.json').write_text(json.dumps(report,indent=2)+'\\n')
print(json.dumps(report),flush=True)
'''
(runtime/'check.py').write_text(driver)
pins=sorted((root/'lean/MicroCFTA').glob('*.lean'))
pins += [root/n for n in ['shell.nix','lean/lean-toolchain','lean/lakefile.toml','lean/lake-manifest.json']]
pins += [source,runtime/'ResourceProbes.lean.txt',strict,independent,runtime/'check.py',Path(__file__)]
(runtime/'source-pins.json').write_text(json.dumps({str(p.relative_to(root)):sha(p) for p in pins},indent=2)+'\n')
(work/'PUBLIC-API-COMPATIBILITY.json').write_text(json.dumps({'prior_checkpoint':promotion['base'],
    'prior_other_source_files_byte_exact':unchanged,'modified_existing_sources':sorted(changed),
    'owner_original_body_preserved':owner.read_bytes().startswith(b'import MicroCFTA.SourcePruningEnumerationSharedSelectedOpaqueObservedResources\n'+(work/'BASE-OWNER.lean.txt').read_bytes()),
    'old_logical_headers_unchanged':True,'new_public_theorems':1,'new_private_resource_probe':1,
    'retained_resource_probes':66},indent=2)+'\n')
print(json.dumps({'run':str(runtime),'objects':str(objects),'public_gates':5,'strict_resource_probes':73}))
