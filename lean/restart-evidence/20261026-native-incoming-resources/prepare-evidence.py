from pathlib import Path
import hashlib,json,re,shutil,subprocess
root=Path('/home/tritlo/Code/mcfta');area=Path('/tmp/mcfta-native-incoming-resources-20261026')
evidence=root/'lean/restart-evidence/20261026-native-incoming-resources'
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
assert {n:r['exit_code'] for n,r in checks.items() if r['exit_code']}=={'strict-conjunction-resources-1':1,'strict-incoming-resources-1':1,'strict-incoming-resources-2':1,'strict-incoming-resources-3':1}
public=(area/'public-final-1/raw.log').read_bytes();text=public.decode()
decls=json.loads((area/'public-declarations.json').read_text())
assert len(re.findall(r'depends on axioms:|does not depend on any axioms',text))==len(decls)==19
assert '⋯' not in text and '...' not in text
for a in re.findall(r'depends on axioms:\s*\[([^]]*)\]',text):
    assert set(re.findall(r'[A-Za-z_.]+',a))<={'propext','Classical.choice','Quot.sound'}
assert len(public)==58470 and len(text.splitlines())==787
assert sha(public)=='fb3c4aea7339580dd1301b0d715bc1f3f9fe9e8b096427638e087c1d1f43d507'
for check in ['strict-audit-1','aggregate-audit-1']:
    assert 'Checked axiom dependencies of 77156 MicroCFTA theorems.' in (area/check/'raw.log').read_text()
oldAudit=git('show',base+':lean/MicroCFTA/Audit.lean')
expected=oldAudit.replace(b'import MicroCFTA.SourcePruningEnumerationRecursiveResources\n',b'import MicroCFTA.SourcePruningEnumerationRecursiveResources\nimport MicroCFTA.SourceCurrentAllocatedConjunctionWorkerResources\nimport MicroCFTA.SourcePruningEnumerationIncomingQueryResources\n',1)
assert (root/'lean/MicroCFTA/Audit.lean').read_bytes()==expected
assert set(git('diff','--name-only',base,'HEAD','--','lean/MicroCFTA').decode().splitlines())==set(sources)
assert not git('diff','--name-only',base,'--','cfta','cfta-generator','specftacular','*.cabal')
main=git('rev-parse','origin/main').decode().strip();assert main=='153e1a211b56dd78bd22f6b427fb78e673041d55'
subprocess.run(['git','merge-base','--is-ancestor',main,'HEAD'],cwd=root,check=True)
unchanged={}
for module in ['SourceCurrentAllocatedTargetQuery','SourceCurrentAllocatedTargetCallerObserved','SourceCurrentAllocatedTargetCallerResources','SourceCurrentAllocatedTargetInitial','SourceCurrentAllocatedNativeComputedBudget','SourceCurrentAllocatedNativeResourceForecast','SourceCurrentConstrainedCapGeneratedQueryResources','SourceCurrentAllocatedPartialInvariant','SourcePruningEnumerationIncomingQuery','SourcePruningEnumerationIncomingNode','SourcePruningEnumerationCachedIncoming','SourcePruningEnumerationCachedFoldCompletion','SourcePruningEnumerationRecursivePacket','SourcePruningEnumerationRecursiveCallback','SourcePruningEnumerationRecursive','SourcePruningEnumerationRecursiveEquations','SourcePruningEnumerationCapturedEdge','SourcePruningEnumerationChildCompletion','SourcePruningEnumerationNativeBranchCompletion','SourcePruningEnumerationNativeContinuations','SourcePruningEnumerationNativeOrdinaryContinuations','SourcePruningEnumerationSelectedStep','SourcePruningEnumerationPrefixCompletion','SourceCurrentAllocatedNativeWordBoundary','SourceCurrentColdFiniteWarmCalls']:
    rel='lean/MicroCFTA/'+module+'.lean';data=(root/rel).read_bytes()
    assert git('show',base+':'+rel)==data,rel
    unchanged[rel]=sha(data)
oldType=(root/'lean/MicroCFTA/SourcePruningEnumerationIncomingQuery.lean').read_text()
newType=(root/'lean/MicroCFTA/SourcePruningEnumerationIncomingQueryResources.lean').read_text()
oldType=oldType[oldType.index('theorem complete\n'):].split(' := by\n',1)[0]
newType=newType[newType.index('theorem complete_resources\n'):].split(' := by\n',1)[0]
oldType=oldType[oldType.index('    ∃ '):].replace('Checked width','Checked (bits + 2)')
newType=newType[newType.index('    ∃ '):].split(' ∧\n      Fits (step profile) queried',1)[0]
assert oldType==newType and len(oldType)==2992
(area/'original-output-proposition.txt').write_text(oldType+'\n')
boundaries=dict(only_existing_source_change_is_two_audit_imports=True,older_interfaces_unchanged=True,runtime_workers_unchanged=True,haskell_unchanged=True,complete_old_incoming_output_preserved=True,old_output_characters=2992,recorded_step_initial_fuel_and_guard_forecast=True,standalone_worker_uses_current_entry_guard_carrier=True,combined_incoming_forecast_uses_original_alphabet_and_profile=True,enabled_worker_allocations_included=True,all_disabled_skipped_performed_paths_preserved=True,exact_original_receipt_memos_post_language_retained=True,initial_explicit_native_worker_reader_ceilings=True,joint_frame_required=False,future_ranges_required=False,future_successful_action_required=False,final_room_claimed=False,actual_incoming_writes_resource_integration_proved=False,full_terminal_fold_resources_proved=False,whole_subtree_completion_proved=False,initial_whole_driver_capacity_proved=False,whole_driver_language_proved=False)
(area/'source-boundaries.json').write_text(json.dumps(boundaries,indent=2)+'\n')
verification=dict(base=base,source_head=git('rev-parse','HEAD').decode().strip(),recorded_main=main,checks=checks,final_strict_modules=finals,final_source_sha256={rel:sha((root/rel).read_bytes()) for rel in sources},unchanged_source_sha256=unchanged,boundaries=boundaries,public_declarations=len(decls),public_lines=len(text.splitlines()),public_bytes=len(public),public_sha256=sha(public),full_definitions=['IncomingQuery.forecast','GeneratedQueryGuardResources.forecast','Room','Fits'],audit_dependencies=77156,aggregate_jobs=3799,goal_status='active')
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
