from pathlib import Path
import hashlib,json,re,shutil,subprocess,gzip
root=Path('/home/tritlo/Code/mcfta');area=Path('/tmp/mcfta-native-terminal-resources-20261026')
evidence=root/'lean/restart-evidence/20261026-native-terminal-resources'
git=lambda *a:subprocess.check_output(['git',*a],cwd=root)
sha=lambda b:hashlib.sha256(b).hexdigest()
base=(area/'base.txt').read_text().strip();finals=json.loads((area/'final-strict.json').read_text())
historical='strict-cached-terminal-adapter-1/MicroCFTA/SourcePruningEnumerationCachedTerminalAdapterResources.lean'
historic=area/historical;compressed=area/(historical+'.gz')
if historic.exists():
    original=historic.read_bytes();compressed.write_bytes(gzip.compress(original,mtime=0));historic.unlink()
original=gzip.decompress(compressed.read_bytes())
report=json.loads((area/'strict-cached-terminal-adapter-1/report.json').read_text())
assert sha(original)==report['source_sha256']
archive=dict(original_path=historical,archive_path=historical+'.gz',original_bytes=len(original),original_sha256=sha(original),restore='Decompress the gzip archive to original_path to replay the historical command. Final source is unchanged.')
(area/'archive-index.json').write_text(json.dumps(archive,indent=2)+'\n')

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
assert {n:r['exit_code'] for n,r in checks.items() if r['exit_code']}=={}
public=(area/'public-final-2/raw.log').read_bytes();text=public.decode()
decls=json.loads((area/'public-declarations.json').read_text())
assert public==(area/'public-final-1/raw.log').read_bytes()
assert len(re.findall(r'depends on axioms:|does not depend on any axioms',text))==len(decls)==20
assert '⋯' not in text and '...' not in text
for a in re.findall(r'depends on axioms:\s*\[([^]]*)\]',text):
    assert set(re.findall(r'[A-Za-z_.]+',a))<={'propext','Classical.choice','Quot.sound'}
assert len(public)==309108 and len(text.splitlines())==2859
assert sha(public)=='3d0fbfb865198da3cd37314c320818971632694e8d3d17c7ecd662d42015e22a'
for check in ['strict-audit-1','aggregate-audit-1']:
    assert 'Checked axiom dependencies of 77268 MicroCFTA theorems.' in (area/check/'raw.log').read_text()
assert 'Build completed successfully (3813 jobs).' in (area/'aggregate-audit-1/raw.log').read_text()
oldAudit=git('show',base+':lean/MicroCFTA/Audit.lean')
expected=oldAudit.replace(b'import MicroCFTA.SourcePruningEnumerationCachedFoldResources\n',b'import MicroCFTA.SourcePruningEnumerationCachedFoldResources\nimport MicroCFTA.SourcePruningEnumerationCachedTerminalResources\nimport MicroCFTA.SourcePruningEnumerationCachedTerminalAdapterResources\n',1)
assert (root/'lean/MicroCFTA/Audit.lean').read_bytes()==expected
assert set(git('diff','--name-only',base,'HEAD','--','lean/MicroCFTA').decode().splitlines())==set(sources)
assert not git('diff','--name-only',base,'--','cfta','cfta-generator','specftacular','*.cabal')
main=git('rev-parse','origin/main').decode().strip();assert main=='153e1a211b56dd78bd22f6b427fb78e673041d55'
subprocess.run(['git','merge-base','--is-ancestor',main,'HEAD'],cwd=root,check=True)
unchanged={}
for module in ['SourceCurrentAllocatedTargetQuery','SourceCurrentAllocatedTargetCallerObserved','SourceCurrentAllocatedTargetCallerResources','SourceCurrentAllocatedTargetCallerGuardResources','SourceCurrentAllocatedConjunctionWorkerResources','SourceCurrentAllocatedTargetInitial','SourceCurrentAllocatedNativeComputedBudget','SourceCurrentAllocatedNativeResourceForecast','SourceCurrentConstrainedCapGeneratedQueryResources','SourceCurrentAllocatedPartialInvariant','SourcePruningEnumerationIncomingQuery','SourcePruningEnumerationIncomingQueryResources','SourcePruningEnumerationIncomingNode','SourcePruningEnumerationCachedIncoming','SourcePruningEnumerationCachedFoldCompletion','SourcePruningEnumerationRecursivePacket','SourcePruningEnumerationRecursiveCallback','SourcePruningEnumerationRecursive','SourcePruningEnumerationRecursiveEquations','SourcePruningEnumerationCapturedEdge','SourcePruningEnumerationChildCompletion','SourcePruningEnumerationNativeBranchCompletion','SourcePruningEnumerationNativeContinuations','SourcePruningEnumerationNativeOrdinaryContinuations','SourcePruningEnumerationSelectedStep','SourcePruningEnumerationPrefixCompletion','SourceCurrentAllocatedNativeWordBoundary','SourcePruningEnumerationIncomingObservedResources','SourcePruningEnumerationIncomingNodeResources','SourcePruningEnumerationCachedIncomingResources','SourcePruningEnumerationCachedDispatch','SourcePruningEnumerationCachedAdapter','SourcePruningEnumerationCachedFold','SourcePruningEnumerationCachedTerminal','SourcePruningEnumerationCachedTerminalAdapter','SourcePruningEnumerationCachedFoldResources','SourcePruningEnumerationFoldAdmission','SourcePruningEnumerationFoldResources','SourcePruningEnumerationIncomingReservation','SourcePruningEnumerationDispatchUnique','SourcePruningEnumerationDispatchResources','SourcePruningEnumerationTerminal','SourcePruningEnumerationTerminalPrefix','SourceCurrentColdFiniteWarmCalls']:
    rel='lean/MicroCFTA/'+module+'.lean';data=(root/rel).read_bytes()
    assert git('show',base+':'+rel)==data,rel
    unchanged[rel]=sha(data)
subprocess.run(['python3',str(area/'contracts.py')],check=True)
contracts=json.loads((area/'old-contracts.json').read_text())
boundaries=dict(only_existing_source_change_is_two_audit_imports=True,older_interfaces_unchanged=True,runtime_workers_unchanged=True,haskell_unchanged=True,complete_old_terminal_output_preserved=True,complete_old_cached_terminal_adapter_output_preserved=True,old_output_contracts=contracts,exact_prefix_and_fold_uniqueness_at_arbitrary_successful_bounds=True,full_old_terminal_ranges_derived_from_current_facts=True,joined_safe_required=False,original_bucket_length_includes_duplicates_and_noops=True,one_original_extra_step_covers_post_fold_incoming_query=True,enabled_empty_allocations_included=True,exact_fold_and_final_native_callers_bounded=True,rejected_fold_retains_completed_prefix_native_effects=True,rejected_fold_incoming_execution_claimed=False,incoming_rejection_keeps_old_cache_receipt=True,safe_remains_conditional_on_nonempty_raw=True,final_room_claimed=False,future_ranges_required=False,future_success_required=False,covered_nonempty_terminal_resource_integration_proved=True,complete_child_resource_integration_proved=False,selected_edge_resources_proved=False,whole_subtree_completion_proved=False,initial_whole_driver_capacity_proved=False,whole_driver_language_proved=False,terminal_outer_fallback_proved=False,host64_capacity_claimed=False,caller_width_conversion_claimed=False)
(area/'source-boundaries.json').write_text(json.dumps(boundaries,indent=2)+'\n')
verification=dict(base=base,source_head=git('rev-parse','HEAD').decode().strip(),recorded_main=main,checks=checks,final_strict_modules=finals,final_source_sha256={rel:sha((root/rel).read_bytes()) for rel in sources},unchanged_source_sha256=unchanged,boundaries=boundaries,public_declarations=len(decls),public_lines=len(text.splitlines()),public_bytes=len(public),public_sha256=sha(public),full_definitions=json.loads((area/'public-definitions.json').read_text()),audit_dependencies=77268,aggregate_jobs=3813,goal_status='active')
(area/'verification.json').write_text(json.dumps(verification,indent=2)+'\n')
(area/'proof-change.patch').write_bytes(git('diff',base,'HEAD','--',*sources))
(area/'original-Audit.lean').write_bytes(oldAudit)
for rel in sources:
    target=area/'sources'/rel;target.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(root/rel,target)
if (evidence/historical).exists():
    assert (evidence/historical).read_bytes()==original
    (evidence/historical).unlink()
shutil.copytree(area,evidence,dirs_exist_ok=True)
manifest={str(p.relative_to(evidence)):dict(bytes=p.stat().st_size,sha256=sha(p.read_bytes())) for p in sorted(evidence.rglob('*')) if p.is_file() and p.name!='manifest.json'}
(evidence/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps(dict(payload_files=len(manifest),payload_bytes=sum(r['bytes'] for r in manifest.values()),manifest_sha256=sha((evidence/'manifest.json').read_bytes()),verification=True),indent=2))
