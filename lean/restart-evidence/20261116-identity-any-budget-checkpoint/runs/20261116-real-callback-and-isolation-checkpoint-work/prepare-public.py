from pathlib import Path
import gzip
import hashlib
import json
import tempfile

root = Path('/home/tritlo/Code/mcfta')
work = Path(__file__).parent
runtime = root / 'lean/restart-evidence/20261116-real-callback-and-isolation-publication'
runtime.mkdir()
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
prior = root / 'lean/restart-evidence/20261116-real-prefix-all-outcome-checkpoint'
old_pins = json.loads(gzip.decompress((prior / 'source-pins.json.gz').read_bytes()))
for name,digest in old_pins.items():
    if name != 'lean/MicroCFTA/Audit.lean':
        assert sha(root / name) == digest, name
assert len([n for n in old_pins if n.startswith('lean/MicroCFTA/') and n != 'lean/MicroCFTA/Audit.lean']) == 6121
assert (work / 'BASE-AUDIT.lean.txt').read_bytes() in (root / 'lean/MicroCFTA/Audit.lean').read_bytes()
old_public = root / 'lean/restart-evidence/20261116-real-prefix-all-outcome-publication'
owner = root / 'lean/MicroCFTA/SourcePruningEnumerationSharedEagerReservation.lean'
probes = (old_public / 'ResourceProbes.lean.txt').read_bytes()
assert probes.count(b'#print axioms ') == 73
(runtime / 'ResourceProbes.lean.txt').write_bytes(probes)
source = runtime / 'source/MicroCFTA' / owner.name
source.parent.mkdir(parents=True)
source.write_bytes(owner.read_bytes()+b'\n'+probes)
objects = Path(tempfile.mkdtemp(prefix='mcfta-callback-isolation-publication-'))
(runtime / 'objects.json').write_text(json.dumps({'path':str(objects)},indent=2)+'\n')
modules = ['SourcePruningEnumerationRealWorkerCallbackResources',
    'SourcePruningEnumerationRealCapturedCallbackResources',
    'SourcePruningEnumerationPrefixIsolatedAtOriginalBudget',
    'SourcePruningEnumerationPrefixNativeReadback']
commands = [['lake','env','lean','-j1','-DwarningAsError=true','-R',str(source.parent.parent),
    '-o',str(objects / 'Owner.olean'),str(source)]]
for name in modules:
    assert (root / 'lean/MicroCFTA' / (name+'.lean')).is_file()
    commands.append(['lake','env','lean','-j1','-DwarningAsError=true',
        '-o',str(objects / (name+'.olean')),str(root / 'lean/MicroCFTA' / (name+'.lean'))])
strict = runtime / 'strict-modules.py'
strict.write_text('import subprocess\ncommands = '+repr(commands)+'\nfor command in commands:\n    subprocess.run(command,check=True)\n')
laws = ['MicroCFTA.SourcePruningEnumerationRealWorkerCallbackResources.recorded_callback_current_at_original_budget',
    'MicroCFTA.SourcePruningEnumerationRealWorkerCallbackResources.real_callback_resources_of_depth_induction',
    'MicroCFTA.SourcePruningEnumerationRealCapturedCallbackResources.completed_real_callback_captured_packet_at_original_budget',
    'MicroCFTA.SourcePruningEnumerationSelectedStep.prefix_isolated_at_original_budget',
    'MicroCFTA.SourcePruningEnumerationSelectedStep.prefix_native_readback_at_original_budget']
independent = runtime / 'IndependentProbes.lean'
text = ''.join('import MicroCFTA.'+name+'\n' for name in modules)
text += (old_public / 'IndependentProbes.lean').read_text()
for qualified in laws:
    text += '\n#check @'+qualified+'\n#print axioms '+qualified+'\n'
independent.write_text(text)
assert text.count('#print axioms ') == 13
template = (root / 'lean/restart-evidence/20261115-native-open-binder-helper-dependencies/check.py').read_text()
driver = template[:template.index('run("public-dependency"')]
jobs = [('public-build','exec lake build',0),
    ('strict-modules-and-73-resources','exec python3 '+str(strict),73),
    ('independent-imports','exec lake env lean -j1 -DwarningAsError=true '+str(independent),13),
    ('audit-build','exec lake build MicroCFTA.Audit',0),
    ('audit-strict','exec lake env lean -j1 -DwarningAsError=true MicroCFTA/Audit.lean',418)]
driver += 'jobs = '+repr(jobs)+'''
for name,command,count in jobs:
    run(name,command,count)
match = re.search(r'Checked axiom dependencies of (\\d+) MicroCFTA theorems\\.',(runtime/'audit-strict.txt').read_text())
assert match and checks[-1]['total_axiom_reports'] == 418
report = {'checks':checks,'source_pins_unchanged':True,'audited_theorems':int(match.group(1)),
    'individual_reports':418,'owner_resource_probes':73,'independent_reports':13,
    'actual_callback_resources_at_original_budget_proved':True,
    'completed_real_callback_restores_captured_packet_proved':True,
    'earlier_isolated_marker_at_original_prefix_budget_proved':True,
    'native_readback_at_original_prefix_budget_proved':True,
    'whole_identity_worker_at_any_budget_proved':False,'whole_real_worker_at_any_budget_proved':False,
    'joint_finite_completion_proved':False,'compiled_haskell_correspondence_proved':False,
    'haskell_changed':False,'at':datetime.datetime.now().astimezone().isoformat(),'limits':limits}
(runtime/'checked.json').write_text(json.dumps(report,indent=2)+'\\n')
print(json.dumps(report),flush=True)
'''
(runtime / 'check.py').write_text(driver)
pins = sorted((root / 'lean/MicroCFTA').glob('*.lean'))
assert len(pins) == 6126
imports = [l for l in (root / 'lean/MicroCFTA/Audit.lean').read_text().splitlines() if l.startswith('import ')]
assert len(imports) == 5126
pins += [root / n for n in ['shell.nix','lean/lean-toolchain','lean/lakefile.toml','lean/lake-manifest.json']]
pins += [source,runtime/'ResourceProbes.lean.txt',strict,independent,runtime/'check.py',Path(__file__)]
(runtime / 'source-pins.json').write_text(json.dumps({str(p.relative_to(root)):sha(p) for p in pins},indent=2)+'\n')
(work / 'PUBLIC-API-COMPATIBILITY.json').write_text(json.dumps({'prior_checkpoint':'ca5a4bcbd0ea06e92d332f50c16190aaa97be4d1',
    'old_non_audit_sources_byte_exact':6121,'old_audit_bytes_retained_as_exact_block':True,
    'source_files':6126,'direct_audit_imports':5126,'new_public_theorems':5,
    'owner_resource_probes':73,'original_headers_and_runtime_budgets_unchanged':True},indent=2)+'\n')
print(json.dumps({'run':str(runtime),'objects':str(objects),'public_gates':5,'source_files':6126,'new_laws':5}))
