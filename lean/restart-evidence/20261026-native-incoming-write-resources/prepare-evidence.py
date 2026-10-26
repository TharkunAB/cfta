from pathlib import Path
import hashlib,json,re,shutil,subprocess
root=Path('/home/tritlo/Code/mcfta');area=Path('/tmp/mcfta-native-incoming-write-resources-20261026')
evidence=root/'lean/restart-evidence/20261026-native-incoming-write-resources'
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
assert {n:r['exit_code'] for n,r in checks.items() if r['exit_code']}=={'strict-node-resources-1':1,'strict-node-resources-2':1,'strict-node-resources-3':1}
public=(area/'public-final-1/raw.log').read_bytes();text=public.decode()
decls=json.loads((area/'public-declarations.json').read_text())
assert len(re.findall(r'depends on axioms:|does not depend on any axioms',text))==len(decls)==17
assert '⋯' not in text and '...' not in text
for a in re.findall(r'depends on axioms:\s*\[([^]]*)\]',text):
    assert set(re.findall(r'[A-Za-z_.]+',a))<={'propext','Classical.choice','Quot.sound'}
assert len(public)==95175 and len(text.splitlines())==1292
assert sha(public)=='b8eda0d1a5cc0f0c9ff83970b267a55244f32eac4dd39f14de734a5022a215bb'
for check in ['strict-audit-1','aggregate-audit-1']:
    assert 'Checked axiom dependencies of 77179 MicroCFTA theorems.' in (area/check/'raw.log').read_text()
assert 'Build completed successfully (3802 jobs).' in (area/'aggregate-audit-1/raw.log').read_text()
oldAudit=git('show',base+':lean/MicroCFTA/Audit.lean')
expected=oldAudit.replace(b'import MicroCFTA.SourcePruningEnumerationIncomingQueryResources\n',b'import MicroCFTA.SourcePruningEnumerationIncomingQueryResources\nimport MicroCFTA.SourcePruningEnumerationCachedIncomingResources\n',1)
assert (root/'lean/MicroCFTA/Audit.lean').read_bytes()==expected
assert set(git('diff','--name-only',base,'HEAD','--','lean/MicroCFTA').decode().splitlines())==set(sources)
assert not git('diff','--name-only',base,'--','cfta','cfta-generator','specftacular','*.cabal')
main=git('rev-parse','origin/main').decode().strip();assert main=='153e1a211b56dd78bd22f6b427fb78e673041d55'
subprocess.run(['git','merge-base','--is-ancestor',main,'HEAD'],cwd=root,check=True)
unchanged={}
for module in ['SourceCurrentAllocatedTargetQuery','SourceCurrentAllocatedTargetCallerObserved','SourceCurrentAllocatedTargetCallerResources','SourceCurrentAllocatedTargetCallerGuardResources','SourceCurrentAllocatedConjunctionWorkerResources','SourceCurrentAllocatedTargetInitial','SourceCurrentAllocatedNativeComputedBudget','SourceCurrentAllocatedNativeResourceForecast','SourceCurrentConstrainedCapGeneratedQueryResources','SourceCurrentAllocatedPartialInvariant','SourcePruningEnumerationIncomingQuery','SourcePruningEnumerationIncomingQueryResources','SourcePruningEnumerationIncomingNode','SourcePruningEnumerationCachedIncoming','SourcePruningEnumerationCachedFoldCompletion','SourcePruningEnumerationRecursivePacket','SourcePruningEnumerationRecursiveCallback','SourcePruningEnumerationRecursive','SourcePruningEnumerationRecursiveEquations','SourcePruningEnumerationCapturedEdge','SourcePruningEnumerationChildCompletion','SourcePruningEnumerationNativeBranchCompletion','SourcePruningEnumerationNativeContinuations','SourcePruningEnumerationNativeOrdinaryContinuations','SourcePruningEnumerationSelectedStep','SourcePruningEnumerationPrefixCompletion','SourceCurrentAllocatedNativeWordBoundary','SourceCurrentColdFiniteWarmCalls']:
    rel='lean/MicroCFTA/'+module+'.lean';data=(root/rel).read_bytes()
    assert git('show',base+':'+rel)==data,rel
    unchanged[rel]=sha(data)
contracts={}
for module,theorem,newTheorem in [('SourcePruningEnumerationIncomingNode','run_complete','run_complete_resources'),('SourcePruningEnumerationCachedIncoming','complete','complete_resources')]:
    oldType=(root/'lean/MicroCFTA'/f'{module}.lean').read_text()
    newType=(root/'lean/MicroCFTA'/f'{module}Resources.lean').read_text()
    oldType=oldType[oldType.index('theorem '+theorem+'\n'):].split(' := by\n',1)[0]
    newType=newType[newType.index('theorem '+newTheorem+'\n'):].split(' := by\n',1)[0]
    oldType=oldType[oldType.index('    ∃ '):].replace('Caller width','Caller (bits + 2)').replace('Checked width','Checked (bits + 2)')
    if module.endswith('IncomingNode'):oldType=oldType.replace('Checked (bits + 2)','SourceEqualityNativeDemand.State (bits + 2)')
    newType=newType[newType.index('    ∃ '):].split(' ∧\n      Fits (',1)[0]
    assert oldType==newType,module
    contracts[module]=dict(retained_characters=len(oldType),output_sha256=sha(oldType.encode()))
    (area/(module+'-original-output.txt')).write_text(oldType+'\n')
assert contracts==json.loads((area/'old-contracts.json').read_text())
boundaries=dict(only_existing_source_change_is_one_audit_import=True,older_interfaces_unchanged=True,runtime_workers_unchanged=True,haskell_unchanged=True,complete_old_node_output_preserved=True,complete_old_cached_output_preserved=True,old_output_contracts=contracts,current_realization_derives_initial_ranges=True,raw_observer_matches_exact_native_and_optional_endpoints=True,raw_observer_covers_every_outer_ok_shape=True,outer_error_converted_to_success=False,combined_incoming_forecast_uses_original_alphabet_and_profile=True,enabled_worker_allocations_included=True,exact_original_receipt_memos_post_language_and_index_retained=True,logical_rejection_cache_separate_from_raw_result=True,rejection_cache_safe_claimed=False,future_ranges_required=False,future_successful_action_required=False,final_room_claimed=False,actual_incoming_writes_resource_integration_proved=True,full_terminal_fold_resources_proved=False,whole_subtree_completion_proved=False,initial_whole_driver_capacity_proved=False,whole_driver_language_proved=False)
(area/'source-boundaries.json').write_text(json.dumps(boundaries,indent=2)+'\n')
verification=dict(base=base,source_head=git('rev-parse','HEAD').decode().strip(),recorded_main=main,checks=checks,final_strict_modules=finals,final_source_sha256={rel:sha((root/rel).read_bytes()) for rel in sources},unchanged_source_sha256=unchanged,boundaries=boundaries,public_declarations=len(decls),public_lines=len(text.splitlines()),public_bytes=len(public),public_sha256=sha(public),full_definitions=['IncomingNode.run','IncomingQuery.forecast','Fits'],audit_dependencies=77179,aggregate_jobs=3802,goal_status='active')
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
