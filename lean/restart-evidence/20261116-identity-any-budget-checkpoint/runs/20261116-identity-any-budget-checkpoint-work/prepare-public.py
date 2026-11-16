from pathlib import Path
import gzip
import hashlib
import json
import tempfile

root = Path('/home/tritlo/Code/mcfta')
work = Path(__file__).parent
runtime = root/'lean/restart-evidence/20261116-identity-any-budget-publication'
runtime.mkdir()
sha = lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
prior = root/'lean/restart-evidence/20261116-real-callback-and-isolation-checkpoint'
old_pins = json.loads(gzip.decompress((prior/'source-pins.json.gz').read_bytes()))
changed = {'lean/MicroCFTA/Audit.lean',
    'lean/MicroCFTA/SourcePruningEnumerationSharedEagerReservation.lean',
    'lean/MicroCFTA/SourcePruningEnumerationRealWorkerCallbackResources.lean',
    'lean/MicroCFTA/SourcePruningEnumerationRealCapturedCallbackResources.lean'}
unchanged = 0
for name,digest in old_pins.items():
    if name not in changed:
        assert sha(root/name) == digest,name
        unchanged += int(name.startswith('lean/MicroCFTA/'))
assert unchanged == 6122
owner = root/'lean/MicroCFTA/SourcePruningEnumerationSharedEagerReservation.lean'
assert (work/'BASE-OWNER.lean.txt').read_bytes() in owner.read_bytes()
assert (work/'BASE-AUDIT.lean.txt').read_bytes() in (root/'lean/MicroCFTA/Audit.lean').read_bytes()
old_work = root/'lean/restart-evidence/20261116-real-callback-and-isolation-checkpoint-work'
probes = (old_work/'Identity61681Probes.lean.txt').read_bytes()
assert probes.count(b'#print axioms ') == 81
(runtime/'ResourceProbes.lean.txt').write_bytes(probes)
source = runtime/'source/MicroCFTA'/owner.name
source.parent.mkdir(parents=True)
source.write_bytes(owner.read_bytes()+b'\n'+probes)
objects = Path(tempfile.mkdtemp(prefix='mcfta-identity-any-budget-publication-'))
(runtime/'objects.json').write_text(json.dumps({'path':str(objects)},indent=2)+'\n')
modules = ['SourcePruningEnumerationRealWorkerCallbackResources',
    'SourcePruningEnumerationRealCapturedCallbackResources',
    'SourcePruningEnumerationPrefixIsolatedAtOriginalBudget',
    'SourcePruningEnumerationPrefixNativeReadback']
commands = [['lake','env','lean','-j1','-DwarningAsError=true','-R',str(source.parent.parent),
    '-o',str(objects/'Owner.olean'),str(source)]]
for name in modules:
    commands.append(['lake','env','lean','-j1','-DwarningAsError=true',
        '-o',str(objects/(name+'.olean')),str(root/'lean/MicroCFTA'/(name+'.lean'))])
strict = runtime/'strict-modules.py'
strict.write_text('import subprocess\ncommands = '+repr(commands)+'\nfor command in commands:\n    subprocess.run(command,check=True)\n')
independent = runtime/'IndependentProbes.lean'
old_public = root/'lean/restart-evidence/20261116-real-callback-and-isolation-publication'
law = 'MicroCFTA.SourcePruningEnumerationSharedEagerReservation.runEager_identity_emitted_resources_at_any_budget'
text = (old_public/'IndependentProbes.lean').read_text()+'\n#check @'+law+'\n#print axioms '+law+'\n'
independent.write_text(text)
assert text.count('#print axioms ') == 14
template = (root/'lean/restart-evidence/20261115-native-open-binder-helper-dependencies/check.py').read_text()
driver = template[:template.index('run("public-dependency"')]
jobs = [('public-build','exec lake build',0),
    ('strict-modules-and-81-resources','exec python3 '+str(strict),81),
    ('independent-imports','exec lake env lean -j1 -DwarningAsError=true '+str(independent),14),
    ('audit-build','exec lake build MicroCFTA.Audit',0),
    ('audit-strict','exec lake env lean -j1 -DwarningAsError=true MicroCFTA/Audit.lean',419)]
driver += 'jobs = '+repr(jobs)+'''
for name,command,count in jobs:
    run(name,command,count)
match = re.search(r'Checked axiom dependencies of (\\d+) MicroCFTA theorems\\.',(runtime/'audit-strict.txt').read_text())
assert match and checks[-1]['total_axiom_reports'] == 419
report = {'checks':checks,'source_pins_unchanged':True,'audited_theorems':int(match.group(1)),
    'individual_reports':419,'owner_resource_probes':81,'independent_reports':14,
    'identity_worker_emitted_resources_at_any_budget_proved':True,
    'original_c831_header_unchanged':True,'callback_proofs_and_public_names_byte_exact':True,
    'callback_import_cycle_removed':True,'whole_real_worker_at_any_budget_proved':False,
    'joint_finite_completion_proved':False,'compiled_haskell_correspondence_proved':False,
    'haskell_changed':False,'at':datetime.datetime.now().astimezone().isoformat(),'limits':limits}
(runtime/'checked.json').write_text(json.dumps(report,indent=2)+'\\n')
print(json.dumps(report),flush=True)
'''
(runtime/'check.py').write_text(driver)
pins = sorted((root/'lean/MicroCFTA').glob('*.lean'))
assert len(pins) == 6126
imports = [l for l in (root/'lean/MicroCFTA/Audit.lean').read_text().splitlines() if l.startswith('import ')]
assert len(imports) == 5126
pins += [root/n for n in ['shell.nix','lean/lean-toolchain','lean/lakefile.toml','lean/lake-manifest.json']]
pins += [source,runtime/'ResourceProbes.lean.txt',strict,independent,runtime/'check.py',Path(__file__)]
(runtime/'source-pins.json').write_text(json.dumps({str(p.relative_to(root)):sha(p) for p in pins},indent=2)+'\n')
(work/'PUBLIC-API-COMPATIBILITY.json').write_text(json.dumps({'prior_checkpoint':'8154da8fc57ef6e032862467eaac32d82ea7ad5b',
    'old_non_audit_sources_byte_exact':6122,'old_owner_and_audit_bytes_retained_as_exact_blocks':True,
    'callback_headers_proofs_and_public_names_byte_exact':True,'new_private_exports':False,
    'source_files':6126,'direct_audit_imports':5126,'new_public_theorems':1,'owner_resource_probes':81,
    'original_headers_and_runtime_budgets_unchanged':True},indent=2)+'\n')
print(json.dumps({'run':str(runtime),'objects':str(objects),'public_gates':5,'owner_reports':81,'independent_reports':14}))
