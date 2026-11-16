from pathlib import Path
import gzip
import hashlib
import json
import tempfile

root=Path('/home/tritlo/Code/mcfta')
work=Path(__file__).parent
private=root/'lean/restart-evidence/20261116-pending-domain-existing-engine-check'
checked=json.loads((private/'checks.json').read_text())
assert all(x['exit']==0 and not x['nonstandard_axioms'] for x in checked)
runtime=root/'lean/restart-evidence/20261116-shared-native-model-publication'
runtime.mkdir()
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
prior=root/'lean/restart-evidence/20261116-native-origin-invariants-checkpoint'
old_pins=json.loads(gzip.decompress((prior/'source-pins.json.gz').read_bytes()))
changed={'lean/MicroCFTA/Audit.lean'}
unchanged=0
for name,digest in old_pins.items():
    if name not in changed:
        assert sha(root/name)==digest,name
        unchanged+=int(name.startswith('lean/MicroCFTA/'))
assert unchanged==6131
owner=root/'lean/MicroCFTA/SourcePruningEnumerationSharedEagerReservation.lean'
assert (work/'BASE-OWNER.lean.txt').read_bytes() in owner.read_bytes()
assert (work/'BASE-AUDIT.lean.txt').read_bytes() in (root/'lean/MicroCFTA/Audit.lean').read_bytes()
probes=(work/'ResourceProbes.lean.txt').read_bytes()
assert probes.count(b'#print axioms ')==136
(runtime/'ResourceProbes.lean.txt').write_bytes(probes)
source=runtime/'source/MicroCFTA'/owner.name
source.parent.mkdir(parents=True)
source.write_bytes(owner.read_bytes()+b'\n'+probes)
objects=Path(tempfile.mkdtemp(prefix='mcfta-real-worker-task-publication-'))
(runtime/'objects.json').write_text(json.dumps({'path':str(objects)},indent=2)+'\n')
modules=['SourcePruningEnumerationRealWorkerCallbackResources', 'SourcePruningEnumerationRealCapturedCallbackResources', 'SourcePruningEnumerationPrefixIsolatedAtOriginalBudget', 'SourcePruningEnumerationPrefixNativeReadback', 'SourcePruningEnumerationRealNullaryCapturedFrameResources', 'SourcePruningEnumerationObservedRealPrefixAdmission', 'SourceCurrentAllocatedNativePastEntryInnerPayloadTransport', 'SourcePruningEnumerationSharedIncomingUnionNormal', 'SourcePruningEnumerationSelectedPrefixUnionNormal', 'SourceCurrentAllocatedNativePastEntryNextQueryInnerLaws', 'SourcePruningEnumerationPreparationUnionNormal', 'SourcePruningEnumerationSharedDispatchUnionNormal', 'SourcePruningEnumerationSharedCachedTerminalUnionNormal', 'SourceCurrentAllocatedNativePastGammaEqualEntryPayload', 'SourcePruningEnumerationSharedChildUnionNormal', 'EnumerationPendingDomainAssignment']
commands=[['lake','env','lean','-j1','-DwarningAsError=true','-R',str(source.parent.parent),
    '-o',str(objects/'Owner.olean'),str(source)]]
for name in modules:
    commands.append(['lake','env','lean','-j1','-DwarningAsError=true',
        '-o',str(objects/(name+'.olean')),str(root/'lean/MicroCFTA'/(name+'.lean'))])
strict=runtime/'strict-modules.py'
strict.write_text('import subprocess\ncommands = '+repr(commands)+'\nfor command in commands:\n    subprocess.run(command,check=True)\n')
independent=runtime/'IndependentProbes.lean'
old_public=root/'lean/restart-evidence/20261116-native-origin-invariants-publication'
laws=['MicroCFTA.SourcePruningEnumerationPreparationUnionNormal.selected_value_unionNormal', 'MicroCFTA.SourcePruningEnumerationPreparationUnionNormal.run_endpoint_unionNormal', 'MicroCFTA.SourcePruningEnumerationSharedDispatchUnionNormal.afterQuery_unionNormal', 'MicroCFTA.SourcePruningEnumerationSharedDispatchUnionNormal.dispatch_unionNormal', 'MicroCFTA.SourcePruningEnumerationSharedCachedTerminalUnionNormal.rawFold_unionNormal', 'MicroCFTA.SourcePruningEnumerationSharedCachedTerminalUnionNormal.fold_unionNormal', 'MicroCFTA.SourcePruningEnumerationSharedCachedTerminalUnionNormal.raw_unionNormal', 'MicroCFTA.SourcePruningEnumerationSharedCachedTerminalUnionNormal.run_unionNormal', 'MicroCFTA.SourceCurrentAllocatedNativePastGammaEqualEntryPayload.old_returned_mixed_profile_after_equal_key_entry', 'MicroCFTA.SourcePruningEnumerationSharedChildUnionNormal.observe_unionNormal', 'MicroCFTA.SourcePruningEnumerationSharedChildUnionNormal.run_unionNormal', 'MicroCFTA.SourcePruningEnumerationSharedChildUnionNormal.traversal_unionNormal', 'MicroCFTA.EnumerationPendingAssignment.stratified_pending_assignment']
text='import MicroCFTA.SourcePruningEnumerationPreparationUnionNormal\nimport MicroCFTA.SourcePruningEnumerationSharedDispatchUnionNormal\nimport MicroCFTA.SourcePruningEnumerationSharedCachedTerminalUnionNormal\nimport MicroCFTA.SourceCurrentAllocatedNativePastGammaEqualEntryPayload\nimport MicroCFTA.SourcePruningEnumerationSharedChildUnionNormal\nimport MicroCFTA.EnumerationPendingDomainAssignment\n'
text+='import MicroCFTA.SourcePruningEnumerationSharedEagerReservation\n'
text+=(old_public/'IndependentProbes.lean').read_text()
for law in laws:text+='\n#check @'+law+'\n#print axioms '+law+'\n'
independent.write_text(text)
assert text.count('#print axioms ')==37
template=(root/'lean/restart-evidence/20261115-native-open-binder-helper-dependencies/check.py').read_text()
driver=template[:template.index('run("public-dependency"')]
jobs=[('public-build','exec lake build',0),
    ('strict-modules-and-136-resources','exec python3 '+str(strict),136),
    ('independent-imports','exec lake env lean -j1 -DwarningAsError=true '+str(independent),37),
    ('audit-build','exec lake build MicroCFTA.Audit',0),
    ('audit-strict','exec lake env lean -j1 -DwarningAsError=true MicroCFTA/Audit.lean',442)]
driver+='jobs = '+repr(jobs)+'''
for name,command,count in jobs:
    run(name,command,count)
match = re.search(r'Checked axiom dependencies of (\\d+) MicroCFTA theorems\\.',(runtime/'audit-strict.txt').read_text())
assert match and checks[-1]['total_axiom_reports'] == 442
report = {'checks':checks,'source_pins_unchanged':True,'audited_theorems':int(match.group(1)),
    'individual_reports':442,'owner_resource_probes':136,'independent_reports':37,
    'identity_worker_emitted_resources_at_any_budget_proved':True,
    'whole_real_worker_at_any_budget_proved':True,'real_task_induction_under_genuine_depth_ih_proved':True,'actual_captured_startup_and_opaque_proved':True,
    'original_real_public_header':'549358aad6c1d3c04f55dbff2a5ab2a9cc61863082c0d955adbb0f293520b607',
    'actual_same_key_past_payload_proved':True,'generic_runtime_equations_proved':8,
    'joint_finite_completion_proved':False,'whole_warm_source_history_proved':False,'next_actual_query_inner_laws_from_past_producers_proved':True,'actual_selected_prefix_union_normal_proved':True,'full_worker_union_normal_proved':False,'actual_selected_preparation_union_normal_proved':True,'actual_shared_dispatch_union_normal_proved':True,'actual_shared_terminal_union_normal_proved':True,'actual_shared_child_union_normal_proved':True,'actual_cold_cell_past_gamma_transport_proved':True,'current_pending_assignment_proved':True,
    'compiled_haskell_correspondence_proved':False,'haskell_changed':False,
    'at':datetime.datetime.now().astimezone().isoformat(),'limits':limits}
(runtime/'checked.json').write_text(json.dumps(report,indent=2)+'\\n')
print(json.dumps(report),flush=True)
'''
driver=driver.replace("+"+repr("\\n"), "+"+repr("\n"))
(runtime/'check.py').write_text(driver)
pins=sorted((root/'lean/MicroCFTA').glob('*.lean'))
assert len(pins)==6138
imports=[l for l in (root/'lean/MicroCFTA/Audit.lean').read_text().splitlines() if l.startswith('import ')]
assert len(imports)==5138
pins += [root/n for n in ['shell.nix','lean/lean-toolchain','lean/lakefile.toml','lean/lake-manifest.json']]
pins += [source,runtime/'ResourceProbes.lean.txt',strict,independent,runtime/'check.py',Path(__file__)]
(runtime/'source-pins.json').write_text(json.dumps({str(p.relative_to(root)):sha(p) for p in pins},indent=2)+'\n')
(work/'PUBLIC-API-COMPATIBILITY.json').write_text(json.dumps({'prior_checkpoint':'0feb93907f8b8f0f49deb4458fe86c6430e261ee',
    'old_non_audit_sources_byte_exact':6131,'old_owner_and_audit_bytes_retained_as_exact_blocks':True,
    'source_files':6138,'direct_audit_imports':5138,'new_public_theorems':13,
    'owner_resource_probes':136,'original_real_header_5493_exact':True,
    'original_runtime_budgets_unchanged':True,'no_future_resource_or_model_provider':True},indent=2)+'\n')
print(json.dumps({'run':str(runtime),'objects':str(objects),'public_gates':5,'owner_reports':136,'independent_reports':37}))
