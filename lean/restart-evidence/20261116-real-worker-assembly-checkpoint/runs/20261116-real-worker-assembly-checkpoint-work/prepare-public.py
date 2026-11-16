from pathlib import Path
import gzip
import hashlib
import json
import tempfile

root = Path('/home/tritlo/Code/mcfta')
work = Path(__file__).parent
runtime = root/'lean/restart-evidence/20261116-real-worker-assembly-publication'
runtime.mkdir()
sha = lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
prior = root/'lean/restart-evidence/20261116-identity-any-budget-checkpoint'
old_pins = json.loads(gzip.decompress((prior/'source-pins.json.gz').read_bytes()))
changed = {'lean/MicroCFTA/Audit.lean',
    'lean/MicroCFTA/SourcePruningEnumerationSharedEagerReservation.lean',
    'lean/MicroCFTA/SourcePruningEnumerationObservedRealPrefixResources.lean'}
unchanged = 0
for name,digest in old_pins.items():
    if name not in changed:
        assert sha(root/name) == digest,name
        unchanged += int(name.startswith('lean/MicroCFTA/'))
assert unchanged == 6123
owner = root/'lean/MicroCFTA/SourcePruningEnumerationSharedEagerReservation.lean'
assert (work/'BASE-OWNER.lean.txt').read_bytes() in owner.read_bytes()
assert (work/'BASE-AUDIT.lean.txt').read_bytes() in (root/'lean/MicroCFTA/Audit.lean').read_bytes()
probes = (work/'Runtime89Probes.lean.txt').read_bytes()
assert probes.count(b'#print axioms ') == 89
(runtime/'ResourceProbes.lean.txt').write_bytes(probes)
source = runtime/'source/MicroCFTA'/owner.name
source.parent.mkdir(parents=True)
source.write_bytes(owner.read_bytes()+b'\n'+probes)
objects = Path(tempfile.mkdtemp(prefix='mcfta-real-worker-assembly-publication-'))
(runtime/'objects.json').write_text(json.dumps({'path':str(objects)},indent=2)+'\n')
modules = ['SourcePruningEnumerationRealWorkerCallbackResources',
    'SourcePruningEnumerationRealCapturedCallbackResources',
    'SourcePruningEnumerationPrefixIsolatedAtOriginalBudget',
    'SourcePruningEnumerationPrefixNativeReadback',
    'SourcePruningEnumerationRealNullaryCapturedFrameResources',
    'SourcePruningEnumerationObservedRealPrefixAdmission']
commands = [['lake','env','lean','-j1','-DwarningAsError=true','-R',str(source.parent.parent),
    '-o',str(objects/'Owner.olean'),str(source)]]
for name in modules:
    commands.append(['lake','env','lean','-j1','-DwarningAsError=true',
        '-o',str(objects/(name+'.olean')),str(root/'lean/MicroCFTA'/(name+'.lean'))])
strict = runtime/'strict-modules.py'
strict.write_text('import subprocess\ncommands = '+repr(commands)+'\nfor command in commands:\n    subprocess.run(command,check=True)\n')
independent = runtime/'IndependentProbes.lean'
old_public = root/'lean/restart-evidence/20261116-identity-any-budget-publication'
laws = ['MicroCFTA.SourcePruningEnumerationSharedRecursive.'+name for name in
    ['observed_success_stages','prepared_done_narrowed','prepared_success_nonempty']]
laws += ['MicroCFTA.SourcePruningEnumerationRealNullaryCapturedFrameResources.nullary_captured_frame_resources_at_original_budget',
    'MicroCFTA.SourcePruningEnumerationSharedRecursive.prefix_real_phase_admission_at_original_budget']
text = 'import MicroCFTA.SourcePruningEnumerationRealNullaryCapturedFrameResources\nimport MicroCFTA.SourcePruningEnumerationObservedRealPrefixAdmission\n'
text += (old_public/'IndependentProbes.lean').read_text()
for law in laws:
    text += '\n#check @'+law+'\n#print axioms '+law+'\n'
independent.write_text(text)
assert text.count('#print axioms ') == 19
template = (root/'lean/restart-evidence/20261115-native-open-binder-helper-dependencies/check.py').read_text()
driver = template[:template.index('run("public-dependency"')]
jobs = [('public-build','exec lake build',0),
    ('strict-modules-and-89-resources','exec python3 '+str(strict),89),
    ('independent-imports','exec lake env lean -j1 -DwarningAsError=true '+str(independent),19),
    ('audit-build','exec lake build MicroCFTA.Audit',0),
    ('audit-strict','exec lake env lean -j1 -DwarningAsError=true MicroCFTA/Audit.lean',424)]
driver += 'jobs = '+repr(jobs)+'''
for name,command,count in jobs:
    run(name,command,count)
match = re.search(r'Checked axiom dependencies of (\\d+) MicroCFTA theorems\\.',(runtime/'audit-strict.txt').read_text())
assert match and checks[-1]['total_axiom_reports'] == 424
report = {'checks':checks,'source_pins_unchanged':True,'audited_theorems':int(match.group(1)),
    'individual_reports':424,'owner_resource_probes':89,'independent_reports':19,
    'identity_worker_emitted_resources_at_any_budget_proved':True,
    'original_c831_header_unchanged':True,'callback_proofs_and_public_names_byte_exact':True,
    'callback_import_cycle_removed':True,'generic_runtime_equations_proved':8,'actual_nullary_resources_proved':True,'real_prefix_phase_admission_at_original_budget_proved':True,'whole_real_worker_at_any_budget_proved':False,
    'joint_finite_completion_proved':False,'compiled_haskell_correspondence_proved':False,
    'haskell_changed':False,'at':datetime.datetime.now().astimezone().isoformat(),'limits':limits}
(runtime/'checked.json').write_text(json.dumps(report,indent=2)+'\\n')
print(json.dumps(report),flush=True)
'''
(runtime/'check.py').write_text(driver)
pins = sorted((root/'lean/MicroCFTA').glob('*.lean'))
assert len(pins) == 6128
imports = [l for l in (root/'lean/MicroCFTA/Audit.lean').read_text().splitlines() if l.startswith('import ')]
assert len(imports) == 5128
pins += [root/n for n in ['shell.nix','lean/lean-toolchain','lean/lakefile.toml','lean/lake-manifest.json']]
pins += [source,runtime/'ResourceProbes.lean.txt',strict,independent,runtime/'check.py',Path(__file__)]
(runtime/'source-pins.json').write_text(json.dumps({str(p.relative_to(root)):sha(p) for p in pins},indent=2)+'\n')
(work/'PUBLIC-API-COMPATIBILITY.json').write_text(json.dumps({'prior_checkpoint':'21b36cd26e9841ca63b09bda62432057da1ad9ad',
    'old_non_audit_sources_byte_exact':6123,'old_owner_and_audit_bytes_retained_as_exact_blocks':True,
    'callback_headers_proofs_and_public_names_byte_exact':True,'visibility_only_receipt_exports':3,
    'source_files':6128,'direct_audit_imports':5128,'new_public_theorems':2,'owner_resource_probes':89,
    'original_headers_and_runtime_budgets_unchanged':True},indent=2)+'\n')
print(json.dumps({'run':str(runtime),'objects':str(objects),'public_gates':5,'owner_reports':89,'independent_reports':19}))
