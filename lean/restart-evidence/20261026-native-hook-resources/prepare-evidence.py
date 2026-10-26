from pathlib import Path
import hashlib,json,re,shutil,subprocess
root=Path('/home/tritlo/Code/mcfta');area=Path('/tmp/mcfta-native-hook-resources-20261026')
evidence=root/'lean/restart-evidence/20261026-native-hook-resources'
git=lambda *a:subprocess.check_output(['git',*a],cwd=root)
sha=lambda b:hashlib.sha256(b).hexdigest()
base=(area/'base.txt').read_text().strip();finals=json.loads((area/'final-strict.json').read_text())
checks={p.parent.name:json.loads(p.read_text()) for p in sorted(area.glob('*/report.json')) if p.parent.name!='contract-evidence'}
sources=['lean/MicroCFTA/'+m+'.lean' for m in finals]
for module,check in finals.items():
    data=(root/'lean/MicroCFTA'/f'{module}.lean').read_bytes();report=checks[check]
    assert report['exit_code']==0 and report['source_sha256']==sha(data)
    assert (area/check/'MicroCFTA'/f'{module}.lean').read_bytes()==data
    assert git('show','HEAD:lean/MicroCFTA/'+module+'.lean')==data
    assert data.endswith(b'\n') and not data.endswith(b'\n\n')
    assert all(line==line.rstrip() for line in data.splitlines())
    if module!='Audit':
        code=re.sub(r'/-[\s\S]*?-/', '', data.decode());code=re.sub(r'--[^\n]*','',code)
        assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',code),module
for check,report in checks.items():
    raw=(area/check/'raw.log').read_bytes()
    assert len(raw)==report['bytes'] and sha(raw)==report['sha256'],check
    assert report['cgroup_limits']=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'},check
assert {n:r['exit_code'] for n,r in checks.items() if r['exit_code']}=={'strict-callback-zero-1':1,'strict-continuation-head-1':1,'strict-hook-1':1,'strict-hook-2':1}
for check in ['helper-build-1','helper-build-2','helper-build-3','install-hook-1','install-callback-final-1','install-ordinary-final-1','strict-audit-1','aggregate-audit-1','public-final-1']:
    assert checks[check]['exit_code']==0
public=(area/'public-final-1/raw.log').read_bytes();text=public.decode()
decls=json.loads((area/'public-declarations.json').read_text());defs=json.loads((area/'public-definitions.json').read_text())
assert len(re.findall(r'depends on axioms:|does not depend on any axioms',text))==len(decls)==14
assert '⋯' not in text and '...' not in text
for a in re.findall(r'depends on axioms:\s*\[([^]]*)\]',text):
    assert set(re.findall(r'[A-Za-z_.]+',a))<={'propext','Classical.choice','Quot.sound'}
assert len(defs)==13 and len(public)==103612 and len(text.splitlines())==1479
assert sha(public)=='a9c42fcae266317968fae9ad031752a72fff6bf5043a04cd5e5c27619d5aa380'
for check in ['strict-audit-1','aggregate-audit-1']:
    assert 'Checked axiom dependencies of 77360 MicroCFTA theorems.' in (area/check/'raw.log').read_text()
assert 'Build completed successfully (3831 jobs).' in (area/'aggregate-audit-1/raw.log').read_text()
oldAudit=git('show',base+':lean/MicroCFTA/Audit.lean')
anchor=b'import MicroCFTA.SourcePruningEnumerationCallbackResources\n'
assert (root/'lean/MicroCFTA/Audit.lean').read_bytes()==oldAudit.replace(anchor,anchor+b'import MicroCFTA.SourcePruningEnumerationOrdinaryHookResources\n',1)
assert set(git('diff','--name-only',base,'HEAD','--','lean/MicroCFTA').decode().splitlines())==set(sources)
assert not git('diff','--name-only',base,'--','cfta','cfta-generator','specftacular','*.cabal')
main=git('rev-parse','origin/main').decode().strip();assert main=='153e1a211b56dd78bd22f6b427fb78e673041d55'
subprocess.run(['git','merge-base','--is-ancestor',main,'HEAD'],cwd=root,check=True)
unchanged={}
for module in ['SourceCurrentColdFiniteWarmCalls','SourcePruningNativeView','SourcePruningOuterNarrow','SourcePruningEnumerationAction','SourcePruningEnumerationSelectedStep','SourcePruningEnumerationPrefixCompletion','SourcePruningEnumerationPrefixPacket','SourcePruningEnumerationRecursivePrefix','SourcePruningEnumerationRecursiveCallback','SourcePruningEnumerationRecursive','SourcePruningEnumerationNativeContinuations','SourcePruningEnumerationNativeBranchPackets','SourceCurrentAllocatedPartialInvariant','SourceCurrentConstrainedCapEditForecast','SourceCurrentConstrainedCapRequiredResources','SourceCurrentProjectionUnionResources']:
    rel='lean/MicroCFTA/'+module+'.lean';data=(root/rel).read_bytes()
    assert git('show',base+':'+rel)==data,rel
    unchanged[rel]=sha(data)
assert unchanged['lean/MicroCFTA/SourceCurrentColdFiniteWarmCalls.lean']=='e4665b0bb522ec88f1925fe6bc360b76e9e4bdfbe6192210ac708a3097a20cc5'
subprocess.run(['python3',str(area/'contracts.py'),'--repo',str(root)],check=True,stdout=subprocess.DEVNULL)
contracts=json.loads((area/'contract-evidence/report.json').read_text())
assert contracts['status']=='PASS'
assert contracts['main_output']['retained_characters']==1313 and contracts['main_output']['retained_clauses']==8
assert contracts['callback_output']['retained_characters']==887 and contracts['callback_output']['generic_continueWith_retained']
for info in contracts['sources'].values(): assert sha(Path(info['path']).read_bytes())==info['sha256']
reviews=''.join((area/name).read_text() for name in ['review-hook.txt','review-ordinary.txt','review-final.txt'])
for name in ['review-hook.txt','review-ordinary.txt','review-final.txt']: assert 'CLEAR' in (area/name).read_text()
for module in finals:
    if module not in ['Audit','SourcePruningEnumerationNativeBranchResources']:
        assert sha((root/'lean/MicroCFTA'/f'{module}.lean').read_bytes()) in reviews,module
oldHead=git('show',base+':lean/MicroCFTA/SourcePruningEnumerationNativeBranchResources.lean')
assert (root/'lean/MicroCFTA/SourcePruningEnumerationNativeBranchResources.lean').read_bytes()==oldHead.replace(
    b'private theorem head_complete_resources',
    b'/-- Original resources derive one actual native alternative and its complete receipt. -/\ntheorem head_complete_resources',1)
(area/'original-NativeBranchResources.lean').write_bytes(oldHead)
content=json.loads((area/'handoff-content.json').read_text())
docs=['NEXT-PROMPT.md','HANDOFF.md','FINDINGS.md','lean/README.md','lean/SYSTEM.md','lean/COVERAGE.md','lean/API-COVERAGE.md','lean/notes-current-system-claim.md','lean/notes-proof-status-20261017.md']
for rel in docs:
    old=git('show',base+':'+rel).decode();new=(root/rel).read_text()
    expected=old.replace('## Original resources now cover actual narrowing and callback prefixes',content['block']+'## Original resources now cover actual narrowing and callback prefixes',1)
    if rel=='FINDINGS.md':expected=expected.replace('### Original resources cover actual narrowing and callback prefixes',content['findings']+'### Original resources cover actual narrowing and callback prefixes',1)
    assert new==expected,rel
assert (root/'lean/notes-current-pruning-enumeration-hook-resources.md').read_text()==content['note']
boundaries={'only_existing_sources_edited_head_module_and_Audit': True, 'head_theorem_only_made_public_with_comment': True, 'head_type_and_proof_exact': True, 'old_public_interfaces_unchanged': True, 'runtime_workers_unchanged': True, 'H6_unchanged': True, 'haskell_unchanged': True, 'genuine_current_Packet_and_IncomingAvoid_required': True, 'original_mixed_reservation_pays_each_actual_reached_head': True, 'duplicates_and_enabled_Empty_allocations_included': True, 'actual_rendered_callback_executed_before_suffix': True, 'actual_zero_recursive_fuel_restart_executed': True, 'original_callback_full_output_and_generic_continuation_equation_retained': True, 'ordinary_wrapper_retains_entire_main_output': True, 'ordinary_entry_called_once_by_runtime': True, 'entry_cache_packet_derived_from_RenderStable_not_false_Frame': True, 'initial_counter_reservation_transported_by_exact_entry_counter': True, 'actual_caller_and_full_memos_threaded_into_suffix': True, 'sibling_captured_cache_and_metadata_restored': True, 'actual_rejection_native_effects_retained': True, 'each_processed_receipt_has_own_Post_and_exact_original_prefix_resources': True, 'each_emitted_output_has_own_callback_Packet_Post_and_edge_prefix_resources': True, 'none_metadata_output_retains_hidden_updated_Packet_witness': True, 'exhausted_current_receipt_kept_outside_processed': True, 'exhausted_current_has_certificate_at_processed_length': True, 'exhausted_stop_retains_exact_caller_query_metadata_and_cache': True, 'unsupported_stop_encodes_no_endpoint': True, 'separate_aggregate_final_Post_and_captured_Packet': True, 'unused_suffix_forecast_padded_without_execution': True, 'query_equality_used_as_full_memo_identity': False, 'Safe_claimed_for_rejected_caches': False, 'identity_hook_used_as_real_callback': False, 'legacy_later_scan_receipts_used_after_hook_stop': False, 'future_callback_or_suffix_success_required': False, 'future_range_or_endpoint_capacity_required': False, 'final_Fits_claims_next_Room': False, 'convergence_or_practical_runtime_claimed': False, 'positive_recursive_expansion_executed_by_new_producer': False, 'whole_selected_expansion_initial_forecast_proved': False, 'whole_recursive_capacity_proved': False, 'whole_driver_language_proved': False, 'host64_capacity_claimed': False, 'concrete_solver_or_Haskell_correspondence_proved': False}
(area/'source-boundaries.json').write_text(json.dumps(boundaries,indent=2)+'\n')
verification=dict(base=base,source_head=git('rev-parse','HEAD').decode().strip(),recorded_main=main,checks=checks,final_strict_modules=finals,final_source_sha256={rel:sha((root/rel).read_bytes()) for rel in sources},unchanged_source_sha256=unchanged,boundaries=boundaries,contracts=contracts,public_declarations=len(decls),public_lines=len(text.splitlines()),public_bytes=len(public),public_sha256=sha(public),full_definitions=defs,audit_dependencies=77360,aggregate_jobs=3831,goal_status='active')
(area/'verification.json').write_text(json.dumps(verification,indent=2)+'\n')
(area/'proof-change.patch').write_bytes(git('diff',base,'HEAD','--',*sources))
assert (area/'original-Audit.lean').read_bytes()==oldAudit
for rel in sources:
    target=area/'sources'/rel;target.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(root/rel,target)
assert not evidence.exists()
shutil.copytree(area,evidence)
manifest={str(p.relative_to(evidence)):dict(bytes=p.stat().st_size,sha256=sha(p.read_bytes())) for p in sorted(evidence.rglob('*')) if p.is_file()}
(evidence/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps(dict(payload_files=len(manifest),payload_bytes=sum(r['bytes'] for r in manifest.values()),manifest_sha256=sha((evidence/'manifest.json').read_bytes()),verification=True),indent=2))
