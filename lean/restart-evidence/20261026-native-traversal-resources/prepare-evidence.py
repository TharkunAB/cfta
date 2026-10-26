from pathlib import Path
import hashlib,json,re,shutil,subprocess
root=Path('/home/tritlo/Code/mcfta'); area=Path('/tmp/mcfta-native-traversal-resources-20261026')
evidence=root/'lean/restart-evidence/20261026-native-traversal-resources'
git=lambda *a:subprocess.check_output(['git',*a],cwd=root)
sha=lambda b:hashlib.sha256(b).hexdigest()
base=(area/'base.txt').read_text().strip(); finals=json.loads((area/'final-strict.json').read_text())
checks={p.parent.name:json.loads(p.read_text()) for p in sorted(area.glob('*/report.json'))}
sources=['lean/MicroCFTA/'+m+'.lean' for m in finals]
for module,check in finals.items():
    data=(root/'lean/MicroCFTA'/f'{module}.lean').read_bytes(); report=checks[check]
    assert report['exit_code']==0 and report['source_sha256']==sha(data)
    assert (area/check/'MicroCFTA'/f'{module}.lean').read_bytes()==data
    assert git('show','HEAD:lean/MicroCFTA/'+module+'.lean')==data
    assert data.endswith(b'\n') and not data.endswith(b'\n\n')
    assert all(line==line.rstrip() for line in data.splitlines())
    if module!='Audit':
        code=re.sub(r'/-[\s\S]*?-/', '', data.decode()); code=re.sub(r'--[^\n]*','',code)
        assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',code),module
for check,report in checks.items():
    raw=(area/check/'raw.log').read_bytes()
    assert len(raw)==report['bytes'] and sha(raw)==report['sha256'],check
    if check.startswith(('helper-build','aggregate','public')): assert report['exit_code']==0,check
assert {n:r['exit_code'] for n,r in checks.items() if r['exit_code']}=={}
public=(area/'public-final-1/raw.log').read_bytes(); text=public.decode()
decls=json.loads((area/'public-declarations.json').read_text())
assert len(re.findall(r'depends on axioms:|does not depend on any axioms',text))==len(decls)==21
assert '⋯' not in text and '...' not in text
for a in re.findall(r'depends on axioms:\s*\[([^]]*)\]',text):
    assert set(re.findall(r'[A-Za-z_.]+',a))<={'propext','Classical.choice','Quot.sound'}
assert len(public)==145533 and len(text.splitlines())==1974
assert sha(public)=='1f849d0e05432827a8b356406cf32222a18406ecc14bb674b5742d3c7ca47392'
for check in ['strict-audit-1','aggregate-audit-1']:
    assert 'Checked axiom dependencies of 77309 MicroCFTA theorems.' in (area/check/'raw.log').read_text()
assert 'Build completed successfully (3820 jobs).' in (area/'aggregate-audit-1/raw.log').read_text()
oldAudit=git('show',base+':lean/MicroCFTA/Audit.lean')
expected=oldAudit.replace(b'import MicroCFTA.SourcePruningEnumerationChildResources\n',b'import MicroCFTA.SourcePruningEnumerationChildResources\nimport MicroCFTA.SourcePruningEnumerationCapturedEdgeResources\n',1)
assert (root/'lean/MicroCFTA/Audit.lean').read_bytes()==expected
assert set(git('diff','--name-only',base,'HEAD','--','lean/MicroCFTA').decode().splitlines())==set(sources)
assert not git('diff','--name-only',base,'--','cfta','cfta-generator','specftacular','*.cabal')
main=git('rev-parse','origin/main').decode().strip(); assert main=='153e1a211b56dd78bd22f6b427fb78e673041d55'
subprocess.run(['git','merge-base','--is-ancestor',main,'HEAD'],cwd=root,check=True)
unchanged={}
for module in ['SourceCurrentAllocatedTargetQuery','SourceCurrentAllocatedTargetCallerObserved','SourceCurrentAllocatedTargetCallerResources','SourceCurrentAllocatedConjunctionWorkerResources','SourceCurrentAllocatedNativeResourceForecast','SourceCurrentConstrainedCapGeneratedQueryResources','SourceCurrentAllocatedPartialInvariant','SourcePruningEnumerationIncomingQuery','SourcePruningEnumerationIncomingQueryResources','SourcePruningEnumerationIncomingNode','SourcePruningEnumerationCachedIncoming','SourcePruningEnumerationCachedFoldCompletion','SourcePruningEnumerationRecursivePacket','SourcePruningEnumerationRecursiveCallback','SourcePruningEnumerationRecursive','SourcePruningEnumerationRecursiveEquations','SourcePruningEnumerationCapturedEdge','SourcePruningEnumerationChildCompletion','SourcePruningEnumerationChildDispatch','SourcePruningEnumerationChildTraversal','SourcePruningEnumerationTraversalCompletion','SourcePruningEnumerationNativeBranchCompletion','SourcePruningEnumerationNativeContinuations','SourcePruningEnumerationNativeOrdinaryContinuations','SourcePruningEnumerationSelectedStep','SourcePruningEnumerationPrefixCompletion','SourceCurrentAllocatedNativeWordBoundary','SourcePruningEnumerationIncomingObservedResources','SourcePruningEnumerationIncomingNodeResources','SourcePruningEnumerationCachedIncomingResources','SourcePruningEnumerationCachedDispatch','SourcePruningEnumerationCachedAdapter','SourcePruningEnumerationCachedFold','SourcePruningEnumerationCachedTerminal','SourcePruningEnumerationCachedTerminalAdapter','SourcePruningEnumerationIncomingReservation','SourcePruningEnumerationDispatchUnique','SourcePruningEnumerationDispatchResources','SourcePruningEnumerationFoldAdmission','SourcePruningEnumerationFoldResources','SourcePruningEnumerationCachedFoldResources','SourcePruningEnumerationTerminalPrefixUnique','SourcePruningEnumerationFoldUnique','SourcePruningEnumerationTerminalAdmission','SourcePruningEnumerationCachedTerminalResources','SourcePruningEnumerationCachedTerminalAdapterResources','SourcePruningEnumerationChildAdmission','SourcePruningEnumerationTerminalObservedResources','SourcePruningEnumerationChildObservedResources','SourcePruningEnumerationChildResources','SourceCurrentColdFiniteWarmCalls']:
    rel='lean/MicroCFTA/'+module+'.lean'; data=(root/rel).read_bytes()
    assert git('show',base+':'+rel)==data,rel
    unchanged[rel]=sha(data)
subprocess.run(['python3',str(area/'contracts.py')],check=True)
contracts=json.loads((area/'old-contracts.json').read_text())
assert len(contracts)==6
expected_counts={'SourcePruningEnumerationTraversalCompletion.complete_with_fragments':2579,'SourcePruningEnumerationTraversalCompletion.complete':2231,'SourcePruningEnumerationSelectedEdge.complete_with_fragments':2088,'SourcePruningEnumerationSelectedEdge.complete':1846,'SourcePruningEnumerationCapturedEdge.complete_with_history':2151,'SourcePruningEnumerationCapturedEdge.complete':1937}
for name,count in expected_counts.items():assert contracts[name]['retained_characters']==count
review=json.loads((area/'independent-review.json').read_text())
assert review['traversal']['source_sha256']==sha((root/'lean/MicroCFTA/SourcePruningEnumerationTraversalResources.lean').read_bytes())
for module,h in review['selected_and_captured']['source_sha256'].items():
    assert h==sha((root/'lean/MicroCFTA'/f'{module}.lean').read_bytes())
boundaries=dict(only_existing_source_change_is_one_audit_import=True,older_interfaces_unchanged=True,runtime_workers_unchanged=True,haskell_unchanged=True,all_six_old_output_contracts_preserved=True,old_output_contracts=contracts,mixed_schedule_uses_only_original_alphabet_profile_actual_child_buckets=True,child_cost_is_sum_of_original_bucket_length_plus_one=True,inherited_and_projected_own_class_descents_both_counted=True,order_and_duplicates_retained=True,mathematical_width_available_from_original_schedule=True,host64_capacity_claimed=False,existing_caller_converted_to_computed_width=False,direct_current_producer_induction=True,entire_old_universally_quantified_traversal_ranges_claimed=False,actual_returned_caller_queries_cache_threaded_through_children=True,genuine_tail_facts_derived_from_post_growth_origin_and_protection=True,enabled_empty_allocations_included=True,original_reservation_split_at_each_actual_child=True,rejection_keeps_completed_prefix_and_stopping_native_effects=True,unused_suffix_execution_claimed=False,own_class_prefix_keeps_native_caller=True,residual_update_keeps_native_caller=True,captured_slot_finalization_keeps_native_caller=True,full_fragment_cache_protection_reference_history_retained=True,exact_captured_write_ancestry_reset_and_stratification_advance_retained=True,safe_conditional_on_completion=True,final_room_claimed=False,future_ranges_required=False,future_success_required=False,supported_arity_and_projected_annotation_gates_required=True,complete_ordered_child_traversal_resources_proved=True,complete_supported_selected_edge_resources_proved=True,complete_captured_slot_resources_proved=True,successive_native_alternative_resource_integration_proved=False,actual_post_callback_subtree_resource_integration_proved=False,whole_subtree_completion_proved=False,initial_whole_driver_capacity_proved=False,whole_driver_language_proved=False)
(area/'source-boundaries.json').write_text(json.dumps(boundaries,indent=2)+'\n')
verification=dict(base=base,source_head=git('rev-parse','HEAD').decode().strip(),recorded_main=main,checks=checks,final_strict_modules=finals,final_source_sha256={rel:sha((root/rel).read_bytes()) for rel in sources},unchanged_source_sha256=unchanged,boundaries=boundaries,public_declarations=len(decls),public_lines=len(text.splitlines()),public_bytes=len(public),public_sha256=sha(public),full_definitions=json.loads((area/'public-definitions.json').read_text()),audit_dependencies=77309,aggregate_jobs=3820,goal_status='active')
(area/'verification.json').write_text(json.dumps(verification,indent=2)+'\n')
(area/'proof-change.patch').write_bytes(git('diff',base,'HEAD','--',*sources))
(area/'original-Audit.lean').write_bytes(oldAudit)
for rel in sources:
    target=area/'sources'/rel; target.parent.mkdir(parents=True,exist_ok=True); shutil.copyfile(root/rel,target)
assert not evidence.exists()
shutil.copytree(area,evidence)
manifest={str(p.relative_to(evidence)):dict(bytes=p.stat().st_size,sha256=sha(p.read_bytes())) for p in sorted(evidence.rglob('*')) if p.is_file()}
(evidence/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps(dict(payload_files=len(manifest),payload_bytes=sum(r['bytes'] for r in manifest.values()),manifest_sha256=sha((evidence/'manifest.json').read_bytes()),verification=True),indent=2))
