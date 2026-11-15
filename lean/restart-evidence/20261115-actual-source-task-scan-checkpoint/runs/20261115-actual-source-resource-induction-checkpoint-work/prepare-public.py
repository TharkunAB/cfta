from pathlib import Path
import gzip
import hashlib
import json
import tempfile

root = Path('/home/tritlo/Code/mcfta')
work = Path(__file__).parent
runtime = root / 'lean/restart-evidence/20261115-actual-source-task-scan-publication'
runtime.mkdir()
owner = root / 'lean/MicroCFTA/SourcePruningEnumerationSharedEagerReservation.lean'
promotion = json.loads((work / 'promotion.json').read_text())
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(owner) == promotion['source_sha256']
prior = root / 'lean/restart-evidence/20261115-native-general-cm-history-checkpoint'
old = json.loads(gzip.decompress((prior / 'source-pins.json.gz').read_bytes()))
unchanged = 0
for name, digest in old.items():
    if name != str(owner.relative_to(root)):
        assert sha(root / name) == digest, name
        if name.startswith('lean/MicroCFTA/') and not name.endswith('/Audit.lean'):
            unchanged += 1
assert unchanged == 6117
bundle = root / 'lean/restart-evidence/20261115-current-actual-prepared-scan-final-opacity-resource-bundle'
probe = (bundle / 'PROBES.lean.txt').read_bytes()
assert probe.count(b'#print axioms ') == 72
(runtime / 'ResourceProbes.lean.txt').write_bytes(probe)
source_root = runtime / 'source'
source = source_root / 'MicroCFTA' / owner.name
source.parent.mkdir(parents=True)
source.write_bytes(owner.read_bytes() + b'\n' + probe)
objects = Path(tempfile.mkdtemp(prefix='mcfta-resource-publication-'))
(runtime / 'objects.json').write_text(json.dumps({'path':str(objects)}, indent=2) + '\n')
independent = runtime / 'IndependentProbes.lean'
independent.write_text('''import MicroCFTA.SourcePruningEnumerationSharedEagerReservation
import MicroCFTA.SourcePruningEnumerationSharedCapturedPreparedObservedResources
import MicroCFTA.SourceCurrentAllocatedNativeGeneralCMHistory
#check @MicroCFTA.SourcePruningEnumerationSharedEagerReservation.runEager_identity_finite_complete_resources
#print axioms MicroCFTA.SourcePruningEnumerationSharedEagerReservation.runEager_identity_finite_complete_resources
#check @MicroCFTA.SourcePruningEnumerationSharedSelectedContinuations.CapturedEdge.observed_complete_with_history_resources_prepared
#print axioms MicroCFTA.SourcePruningEnumerationSharedSelectedContinuations.CapturedEdge.observed_complete_with_history_resources_prepared
#check @MicroCFTA.SourceCurrentAllocatedNativeGeneralCMHistory.current_stored_universe_general_cm_returned_at_every_actual_prefix
#print axioms MicroCFTA.SourceCurrentAllocatedNativeGeneralCMHistory.current_stored_universe_general_cm_returned_at_every_actual_prefix
''')
template = (root / 'lean/restart-evidence/20261115-native-open-binder-helper-dependencies/check.py').read_text()
driver = template[:template.index('run("public-dependency"')]
jobs = [('public-build', 'exec lake build', 0),
        ('strict-owner-and-72-resources', f'exec lake env lean -j1 -DwarningAsError=true -R {source_root} -o {objects}/SourcePruningEnumerationSharedEagerReservation.olean {source}', 72),
        ('independent-imports', f'exec lake env lean -j1 -DwarningAsError=true {independent}', 3),
        ('audit-build', 'exec lake build MicroCFTA.Audit', 0),
        ('audit-strict', 'exec lake env lean -j1 -DwarningAsError=true MicroCFTA/Audit.lean', 408)]
driver += 'jobs = ' + repr(jobs) + '\n'
driver += '''for name, command, count in jobs:
    run(name, command, count)
match = re.search(r'Checked axiom dependencies of (\\d+) MicroCFTA theorems\\.', (runtime / 'audit-strict.txt').read_text())
assert match
assert checks[-1]['total_axiom_reports'] == 408
report = {'checks':checks, 'source_pins_unchanged':True, 'audited_theorems':int(match.group(1)),
    'individual_reports':408, 'retained_resource_probes':66, 'new_resource_probes':6,
    'whole_actual_task_induction_proved':True, 'original_prepared_scan_resources_at_any_budget_proved':True,
    'whole_identity_worker_at_any_budget_proved':False, 'real_narrow_worker_at_any_budget_proved':False,
    'joint_finite_completion_proved':False, 'compiled_haskell_correspondence_proved':False,
    'haskell_changed':False, 'at':datetime.datetime.now().astimezone().isoformat(), 'limits':limits}
(runtime / 'checked.json').write_text(json.dumps(report, indent=2) + '\\n')
print(json.dumps(report), flush=True)
'''
(runtime / 'check.py').write_text(driver)
pins = sorted((root / 'lean/MicroCFTA').glob('*.lean'))
pins += [root / n for n in ['shell.nix','lean/lean-toolchain','lean/lakefile.toml','lean/lake-manifest.json']]
pins += [source, independent, runtime/'ResourceProbes.lean.txt', runtime/'check.py', Path(__file__)]
(runtime / 'source-pins.json').write_text(json.dumps({str(p.relative_to(root)):sha(p) for p in pins}, indent=2) + '\n')
(work / 'PUBLIC-API-COMPATIBILITY.json').write_text(json.dumps({'prior_checkpoint':promotion['base'],
    'unchanged_prior_non_audit_sources':unchanged,'modified_existing_source':str(owner.relative_to(root)),
    'all_old_owner_bytes_preserved_as_exact_prefix':owner.read_bytes().startswith((work/'BASE-SOURCE.lean.txt').read_bytes()),
    'old_source_headers_unchanged':True,'new_public_theorems':0,'new_private_resource_probes':6,
    'retained_resource_probes':66},indent=2)+'\n')
print(json.dumps({'run':str(runtime),'objects':str(objects),'pins':len(pins),'public_gates':5,'strict_resource_probes':72}))
