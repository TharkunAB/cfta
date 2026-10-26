from pathlib import Path
import hashlib,json,re,shutil,subprocess
root=Path('/home/tritlo/Code/mcfta'); area=Path('/tmp/mcfta-native-alternative-resources-20261026')
evidence=root/'lean/restart-evidence/20261026-native-alternative-resources'
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
assert {n:r['exit_code'] for n,r in checks.items() if r['exit_code']}=={'strict-native-resources-1':1,'strict-native-packets-1':1,'strict-native-packets-2':1}
public=(area/'public-final-1/raw.log').read_bytes(); text=public.decode()
decls=json.loads((area/'public-declarations.json').read_text())
assert len(re.findall(r'depends on axioms:|does not depend on any axioms',text))==len(decls)==17
assert '⋯' not in text and '...' not in text
for a in re.findall(r'depends on axioms:\s*\[([^]]*)\]',text):
    assert set(re.findall(r'[A-Za-z_.]+',a))<={'propext','Classical.choice','Quot.sound'}
assert len(public)==92368 and len(text.splitlines())==1297
assert sha(public)=='90ba026e6c5c8d31b996f983d4d9cd915d68a82c13126d12f357c34c3ffe554f'
for check in ['strict-audit-1','aggregate-audit-1']:
    assert 'Checked axiom dependencies of 77323 MicroCFTA theorems.' in (area/check/'raw.log').read_text()
assert 'Build completed successfully (3822 jobs).' in (area/'aggregate-audit-1/raw.log').read_text()
oldAudit=git('show',base+':lean/MicroCFTA/Audit.lean')
expected=oldAudit.replace(b'import MicroCFTA.SourcePruningEnumerationCapturedEdgeResources\n',b'import MicroCFTA.SourcePruningEnumerationCapturedEdgeResources\nimport MicroCFTA.SourcePruningEnumerationNativeBranchPackets\n',1)
assert (root/'lean/MicroCFTA/Audit.lean').read_bytes()==expected
assert set(git('diff','--name-only',base,'HEAD','--','lean/MicroCFTA').decode().splitlines())==set(sources)
assert not git('diff','--name-only',base,'--','cfta','cfta-generator','specftacular','*.cabal')
main=git('rev-parse','origin/main').decode().strip(); assert main=='153e1a211b56dd78bd22f6b427fb78e673041d55'
subprocess.run(['git','merge-base','--is-ancestor',main,'HEAD'],cwd=root,check=True)
unchanged={}
for module in ['SourceCurrentAllocatedTargetQuery','SourceCurrentAllocatedTargetCallerObserved','SourceCurrentAllocatedTargetCallerResources','SourceCurrentAllocatedConjunctionWorkerResources','SourceCurrentAllocatedNativeResourceForecast','SourceCurrentConstrainedCapGeneratedQueryResources','SourceCurrentAllocatedPartialInvariant','SourcePruningEnumerationIncomingQuery','SourcePruningEnumerationIncomingQueryResources','SourcePruningEnumerationIncomingNode','SourcePruningEnumerationCachedIncoming','SourcePruningEnumerationCachedFoldCompletion','SourcePruningEnumerationRecursivePacket','SourcePruningEnumerationRecursiveCallback','SourcePruningEnumerationRecursive','SourcePruningEnumerationRecursiveEquations','SourcePruningEnumerationCapturedEdge','SourcePruningEnumerationChildCompletion','SourcePruningEnumerationChildDispatch','SourcePruningEnumerationChildTraversal','SourcePruningEnumerationTraversalCompletion','SourcePruningEnumerationNativeBranchCompletion','SourcePruningEnumerationNativeContinuations','SourcePruningEnumerationNativeOrdinaryContinuations','SourcePruningEnumerationSelectedStep','SourcePruningEnumerationPrefixCompletion','SourceCurrentAllocatedNativeWordBoundary','SourcePruningEnumerationIncomingObservedResources','SourcePruningEnumerationIncomingNodeResources','SourcePruningEnumerationCachedIncomingResources','SourcePruningEnumerationCachedDispatch','SourcePruningEnumerationCachedAdapter','SourcePruningEnumerationCachedFold','SourcePruningEnumerationCachedTerminal','SourcePruningEnumerationCachedTerminalAdapter','SourcePruningEnumerationIncomingReservation','SourcePruningEnumerationDispatchUnique','SourcePruningEnumerationDispatchResources','SourcePruningEnumerationFoldAdmission','SourcePruningEnumerationFoldResources','SourcePruningEnumerationCachedFoldResources','SourcePruningEnumerationTerminalPrefixUnique','SourcePruningEnumerationFoldUnique','SourcePruningEnumerationTerminalAdmission','SourcePruningEnumerationCachedTerminalResources','SourcePruningEnumerationCachedTerminalAdapterResources','SourcePruningEnumerationChildAdmission','SourcePruningEnumerationTerminalObservedResources','SourcePruningEnumerationChildObservedResources','SourcePruningEnumerationChildResources','SourcePruningEnumerationTraversalResources','SourcePruningEnumerationSelectedEdgeResources','SourcePruningEnumerationCapturedEdgeResources','SourcePruningEnumerationNativeCacheGrowth','SourcePruningEnumerationNativeBranches','SourcePruningEnumerationRecursivePrefix','SourcePruningEnumerationNativeBranchCompletion','SourceCurrentColdFiniteWarmCalls']:
    rel='lean/MicroCFTA/'+module+'.lean'; data=(root/rel).read_bytes()
    assert git('show',base+':'+rel)==data,rel
    unchanged[rel]=sha(data)
subprocess.run(['python3',str(area/'contracts.py')],check=True)
contracts=json.loads((area/'old-contracts.json').read_text())
assert len(contracts)==5
expected_counts={'SourcePruningEnumerationNativeBranchResources.complete_with_history_resources':1406,'SourcePruningEnumerationNativeBranchResources.complete_with_posts_resources':1337,'SourcePruningEnumerationNativeBranchResources.complete_resources':1013,'SourcePruningEnumerationNativeBranchPackets.complete_with_packets_resources':1406,'SourcePruningEnumerationNativeBranchPackets.strengthened_resource_packet':2214}
for name,count in expected_counts.items():assert contracts[name]['retained_characters']==count
review=json.loads((area/'independent-review.json').read_text())
assert review['native_resources']['final_source_sha256']==sha((root/'lean/MicroCFTA/SourcePruningEnumerationNativeBranchResources.lean').read_bytes())
assert review['native_packets']['final_source_sha256']==sha((root/'lean/MicroCFTA/SourcePruningEnumerationNativeBranchPackets.lean').read_bytes())
for check in ['strict-audit-1','aggregate-audit-1','public-final-1']:
    assert checks[check]['cgroup_limits']=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
boundaries=dict(only_existing_source_change_is_one_audit_import=True,older_interfaces_unchanged=True,runtime_workers_unchanged=True,haskell_unchanged=True,all_three_old_scan_output_contracts_preserved=True,old_output_contracts=contracts,packet_wrapper_keeps_entire_strengthened_resource_output=True,mixed_schedule_uses_only_original_alphabet_profile_actual_edge_costs=True,arity_rejection_and_unsupported_cost_zero=True,supported_edge_cost_counts_actual_projected_child_inputs=True,ordered_cost_includes_duplicate_alternatives=True,mathematical_width_available_from_original_schedule=True,host64_capacity_claimed=False,existing_caller_converted_to_computed_width=False,direct_current_producer_induction=True,entire_old_future_universal_ranges_claimed=False,same_captured_enumeration_cache_restored_each_alternative=True,actual_returned_caller_queries_and_full_memos_threaded=True,valid_child_rejection_retains_native_effects_and_continues=True,captured_realization_flags_decode_transported_by_actual_post=True,enabled_empty_allocations_included=True,original_reservation_split_at_each_reached_alternative=True,unsupported_projection_retains_explicit_stop=True,unused_suffix_execution_claimed=False,final_caller_fits_and_guard_carrier=True,each_processed_receipt_has_exact_original_take_prefix_resources=True,earlier_receipt_cache_retargeted_to_final_heap=False,packet_wrapper_adds_no_initial_producer_premise=True,conditional_packet_uses_original_packet_and_incoming_avoid=True,full_post_memos_retained_without_query_only_identification=True,completed_receipt_own_and_original_captured_cache_packets_at_same_actual_caller=True,safe_packet_claimed_for_rejected_receipts=False,final_room_claimed=False,future_ranges_required=False,future_success_required=False,legacy_ordered_native_alternative_resources_proved=True,actual_callback_hook_executed_by_new_producer=False,post_recursive_subtree_sibling_resource_integration_proved=False,whole_subtree_completion_proved=False,initial_whole_driver_capacity_proved=False,whole_driver_language_proved=False)
(area/'source-boundaries.json').write_text(json.dumps(boundaries,indent=2)+'\n')
verification=dict(base=base,source_head=git('rev-parse','HEAD').decode().strip(),recorded_main=main,checks=checks,final_strict_modules=finals,final_source_sha256={rel:sha((root/rel).read_bytes()) for rel in sources},unchanged_source_sha256=unchanged,boundaries=boundaries,public_declarations=len(decls),public_lines=len(text.splitlines()),public_bytes=len(public),public_sha256=sha(public),full_definitions=json.loads((area/'public-definitions.json').read_text()),audit_dependencies=77323,aggregate_jobs=3822,goal_status='active')
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
