from pathlib import Path
import hashlib,json,re,shutil,subprocess
root=Path('/home/tritlo/Code/mcfta');area=Path('/tmp/mcfta-native-incoming-fold-resources-20261026')
evidence=root/'lean/restart-evidence/20261026-native-incoming-fold-resources'
git=lambda *a:subprocess.check_output(['git',*a],cwd=root)
sha=lambda b:hashlib.sha256(b).hexdigest()
base=(area/'base.txt').read_text().strip();finals=json.loads((area/'final-strict.json').read_text())
checks={p.parent.name:json.loads(p.read_text()) for p in sorted(area.glob('*/report.json'))}
sources=['lean/MicroCFTA/'+m+'.lean' for m in finals]
for module,check in finals.items():
    data=(root/'lean/MicroCFTA'/f'{module}.lean').read_bytes();report=checks[check]
    assert report['exit_code']==0 and report['source_sha256']==sha(data)
    assert (area/check/'MicroCFTA'/f'{module}.lean').read_bytes()==data
    assert git('show','HEAD:lean/MicroCFTA/'+module+'.lean')==data
    if module!='Audit':
        code=re.sub(r'/-[\s\S]*?-/', '', data.decode());code=re.sub(r'--[^\n]*','',code)
        assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',code),module
for check,report in checks.items():
    raw=(area/check/'raw.log').read_bytes()
    assert len(raw)==report['bytes'] and sha(raw)==report['sha256'],check
    if check.startswith(('helper-build','aggregate','public')): assert report['exit_code']==0,check
assert {n:r['exit_code'] for n,r in checks.items() if r['exit_code']}=={'strict-dispatch-1':1,'strict-admission-1':1,'strict-fold-resources-1':1,'strict-reservation-2':1}
public=(area/'public-final-1/raw.log').read_bytes();text=public.decode()
decls=json.loads((area/'public-declarations.json').read_text())
assert len(re.findall(r'depends on axioms:|does not depend on any axioms',text))==len(decls)==21
assert '⋯' not in text and '...' not in text
for a in re.findall(r'depends on axioms:\s*\[([^]]*)\]',text):
    assert set(re.findall(r'[A-Za-z_.]+',a))<={'propext','Classical.choice','Quot.sound'}
assert len(public)==77723 and len(text.splitlines())==1014
assert sha(public)=='1de94099511cebd0bbbff53896ad45d93bf71766ee139b7c423ed79bed33ed0d'
for check in ['strict-audit-1','aggregate-audit-1']:
    assert 'Checked axiom dependencies of 77249 MicroCFTA theorems.' in (area/check/'raw.log').read_text()
assert 'Build completed successfully (3808 jobs).' in (area/'aggregate-audit-1/raw.log').read_text()
oldAudit=git('show',base+':lean/MicroCFTA/Audit.lean')
expected=oldAudit.replace(b'import MicroCFTA.SourcePruningEnumerationCachedIncomingResources\n',b'import MicroCFTA.SourcePruningEnumerationCachedIncomingResources\nimport MicroCFTA.SourcePruningEnumerationCachedFoldResources\n',1)
assert (root/'lean/MicroCFTA/Audit.lean').read_bytes()==expected
assert set(git('diff','--name-only',base,'HEAD','--','lean/MicroCFTA').decode().splitlines())==set(sources)
assert not git('diff','--name-only',base,'--','cfta','cfta-generator','specftacular','*.cabal')
main=git('rev-parse','origin/main').decode().strip();assert main=='153e1a211b56dd78bd22f6b427fb78e673041d55'
subprocess.run(['git','merge-base','--is-ancestor',main,'HEAD'],cwd=root,check=True)
unchanged={}
for module in ['SourceCurrentAllocatedTargetQuery','SourceCurrentAllocatedTargetCallerObserved','SourceCurrentAllocatedTargetCallerResources','SourceCurrentAllocatedTargetCallerGuardResources','SourceCurrentAllocatedConjunctionWorkerResources','SourceCurrentAllocatedTargetInitial','SourceCurrentAllocatedNativeComputedBudget','SourceCurrentAllocatedNativeResourceForecast','SourceCurrentConstrainedCapGeneratedQueryResources','SourceCurrentAllocatedPartialInvariant','SourcePruningEnumerationIncomingQuery','SourcePruningEnumerationIncomingQueryResources','SourcePruningEnumerationIncomingNode','SourcePruningEnumerationCachedIncoming','SourcePruningEnumerationCachedFoldCompletion','SourcePruningEnumerationRecursivePacket','SourcePruningEnumerationRecursiveCallback','SourcePruningEnumerationRecursive','SourcePruningEnumerationRecursiveEquations','SourcePruningEnumerationCapturedEdge','SourcePruningEnumerationChildCompletion','SourcePruningEnumerationNativeBranchCompletion','SourcePruningEnumerationNativeContinuations','SourcePruningEnumerationNativeOrdinaryContinuations','SourcePruningEnumerationSelectedStep','SourcePruningEnumerationPrefixCompletion','SourceCurrentAllocatedNativeWordBoundary','SourcePruningEnumerationIncomingObservedResources','SourcePruningEnumerationIncomingNodeResources','SourcePruningEnumerationCachedIncomingResources','SourcePruningEnumerationCachedDispatch','SourcePruningEnumerationCachedAdapter','SourcePruningEnumerationCachedFold','SourcePruningEnumerationCachedTerminal','SourcePruningEnumerationCachedTerminalAdapter','SourceCurrentColdFiniteWarmCalls']:
    rel='lean/MicroCFTA/'+module+'.lean';data=(root/rel).read_bytes()
    assert git('show',base+':'+rel)==data,rel
    unchanged[rel]=sha(data)
subprocess.run(['python3',str(area/'contracts.py')],check=True)
contracts=json.loads((area/'old-contracts.json').read_text())
boundaries=dict(only_existing_source_change_is_one_audit_import=True,older_interfaces_unchanged=True,runtime_workers_unchanged=True,haskell_unchanged=True,complete_old_dispatch_output_preserved=True,complete_old_cached_fold_output_preserved=True,old_output_contracts=contracts,mixed_schedule_uses_only_original_alphabet_profile_count=True,mathematical_width_computed_from_original_schedule=True,host64_capacity_claimed=False,existing_caller_converted_to_computed_width=False,dispatch_uniqueness_includes_action_entire_caller_and_query_memo=True,full_old_future_universal_fold_ranges_derived_from_current_facts=True,arbitrary_singletons_retain_full_next_initial_packet=True,enabled_empty_allocations_included=True,raw_fold_observer_matches_exact_final_caller=True,raw_fold_observer_covers_every_outer_ok_shape=True,outer_error_converted_to_success=False,outer_error_endpoint_resources_claimed=False,rejected_fold_retains_completed_prefix_native_effects=True,unused_suffix_execution_claimed=False,final_room_claimed=False,future_ranges_required=False,future_success_required=False,complete_ordered_cached_fold_resource_integration_proved=True,full_terminal_join_and_incoming_resource_integration_proved=False,whole_subtree_completion_proved=False,initial_whole_driver_capacity_proved=False,whole_driver_language_proved=False)
(area/'source-boundaries.json').write_text(json.dumps(boundaries,indent=2)+'\n')
verification=dict(base=base,source_head=git('rev-parse','HEAD').decode().strip(),recorded_main=main,checks=checks,final_strict_modules=finals,final_source_sha256={rel:sha((root/rel).read_bytes()) for rel in sources},unchanged_source_sha256=unchanged,boundaries=boundaries,public_declarations=len(decls),public_lines=len(text.splitlines()),public_bytes=len(public),public_sha256=sha(public),full_definitions=json.loads((area/'public-definitions.json').read_text()),audit_dependencies=77249,aggregate_jobs=3808,goal_status='active')
(area/'verification.json').write_text(json.dumps(verification,indent=2)+'\n')
(area/'proof-change.patch').write_bytes(git('diff',base,'HEAD','--',*sources))
(area/'original-Audit.lean').write_bytes(oldAudit)
for rel in sources:
    target=area/'sources'/rel;target.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(root/rel,target)
assert not evidence.exists()
shutil.copytree(area,evidence)
manifest={str(p.relative_to(evidence)):dict(bytes=p.stat().st_size,sha256=sha(p.read_bytes())) for p in sorted(evidence.rglob('*')) if p.is_file()}
(evidence/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps(dict(payload_files=len(manifest),payload_bytes=sum(r['bytes'] for r in manifest.values()),manifest_sha256=sha((evidence/'manifest.json').read_bytes()),verification=True),indent=2))
