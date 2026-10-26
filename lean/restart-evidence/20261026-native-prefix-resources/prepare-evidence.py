from pathlib import Path
import hashlib,json,re,shutil,subprocess
root=Path('/home/tritlo/Code/mcfta');area=Path('/tmp/mcfta-native-prefix-resources-20261026')
evidence=root/'lean/restart-evidence/20261026-native-prefix-resources'
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
    assert data.endswith(b'\n') and not data.endswith(b'\n\n')
    assert all(line==line.rstrip() for line in data.splitlines())
    if module!='Audit':
        code=re.sub(r'/-[\s\S]*?-/', '', data.decode());code=re.sub(r'--[^\n]*','',code)
        assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',code),module
for check,report in checks.items():
    raw=(area/check/'raw.log').read_bytes()
    assert len(raw)==report['bytes'] and sha(raw)==report['sha256'],check
    assert report['cgroup_limits']=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'},check
assert {n:r['exit_code'] for n,r in checks.items() if r['exit_code']}=={'strict-prefix-1':1,'strict-prefix-2':1}
for check in ['install-narrow-1','install-prefix-1','install-callback-1','strict-audit-1','aggregate-audit-1','public-final-1']:
    assert checks[check]['exit_code']==0
public=(area/'public-final-1/raw.log').read_bytes();text=public.decode()
decls=json.loads((area/'public-declarations.json').read_text());defs=json.loads((area/'public-definitions.json').read_text())
assert len(re.findall(r'depends on axioms:|does not depend on any axioms',text))==len(decls)==11
assert '⋯' not in text and '...' not in text
for a in re.findall(r'depends on axioms:\s*\[([^]]*)\]',text):
    assert set(re.findall(r'[A-Za-z_.]+',a))<={'propext','Classical.choice','Quot.sound'}
assert len(defs)==8 and len(public)==61360 and len(text.splitlines())==850
assert sha(public)=='74b5bbad3c21e4b8a082222181957bbaec9caa1e4565de05f28619c2e84323bb'
for check in ['strict-audit-1','aggregate-audit-1']:
    assert 'Checked axiom dependencies of 77331 MicroCFTA theorems.' in (area/check/'raw.log').read_text()
assert 'Build completed successfully (3825 jobs).' in (area/'aggregate-audit-1/raw.log').read_text()
oldAudit=git('show',base+':lean/MicroCFTA/Audit.lean')
anchor=b'import MicroCFTA.SourcePruningEnumerationNativeBranchPackets\n'
assert (root/'lean/MicroCFTA/Audit.lean').read_bytes()==oldAudit.replace(anchor,anchor+b'import MicroCFTA.SourcePruningEnumerationCallbackResources\n',1)
assert set(git('diff','--name-only',base,'HEAD','--','lean/MicroCFTA').decode().splitlines())==set(sources)
assert not git('diff','--name-only',base,'--','cfta','cfta-generator','specftacular','*.cabal')
main=git('rev-parse','origin/main').decode().strip();assert main=='153e1a211b56dd78bd22f6b427fb78e673041d55'
subprocess.run(['git','merge-base','--is-ancestor',main,'HEAD'],cwd=root,check=True)
unchanged={}
for module in ['SourceCurrentColdFiniteWarmCalls','SourcePruningNativeView','SourcePruningOuterNarrow','SourcePruningEnumerationAction','SourcePruningEnumerationSelectedStep','SourcePruningEnumerationPrefixCompletion','SourcePruningEnumerationPrefixPacket','SourcePruningEnumerationRecursivePrefix','SourcePruningEnumerationRecursiveCallback','SourcePruningEnumerationRecursive','SourcePruningEnumerationNativeContinuations','SourcePruningEnumerationNativeBranchResources','SourcePruningEnumerationNativeBranchPackets','SourceCurrentAllocatedPartialInvariant','SourceCurrentConstrainedCapEditForecast','SourceCurrentConstrainedCapRequiredResources','SourceCurrentProjectionUnionResources']:
    rel='lean/MicroCFTA/'+module+'.lean';data=(root/rel).read_bytes()
    assert git('show',base+':'+rel)==data,rel
    unchanged[rel]=sha(data)
assert unchanged['lean/MicroCFTA/SourceCurrentColdFiniteWarmCalls.lean']=='e4665b0bb522ec88f1925fe6bc360b76e9e4bdfbe6192210ac708a3097a20cc5'
subprocess.run(['python3',str(area/'contracts.py')],check=True)
contracts=json.loads((area/'old-contracts.json').read_text())
assert contracts['callback_complete_entire_output']['retained_characters']==1390
assert contracts['prefix_complete_entire_output']['retained_characters']==406
review=(area/'review-guard.txt').read_text();assert 'CLEAR' in review
for module in finals:
    if module!='Audit': assert sha((root/'lean/MicroCFTA'/f'{module}.lean').read_bytes()) in review
content=json.loads((area/'handoff-content.json').read_text())
docs=['NEXT-PROMPT.md','HANDOFF.md','FINDINGS.md','lean/README.md','lean/SYSTEM.md','lean/COVERAGE.md','lean/API-COVERAGE.md','lean/notes-current-system-claim.md','lean/notes-proof-status-20261017.md']
for rel in docs:
    old=git('show',base+':'+rel).decode();new=(root/rel).read_text()
    expected=old.replace('## Original reservations now cover native alternatives and receipt packets',content['block']+'## Original reservations now cover native alternatives and receipt packets',1)
    if rel=='FINDINGS.md':expected=expected.replace('### Original resources cover native alternatives and receipt packets',content['findings']+'### Original resources cover native alternatives and receipt packets',1)
    assert new==expected,rel
assert (root/'lean/notes-current-pruning-enumeration-prefix-resources.md').read_text()==content['note']
boundaries=dict(only_existing_source_edit_one_Audit_import=True,old_interfaces_unchanged=True,runtime_workers_unchanged=True,H6_unchanged=True,haskell_unchanged=True,original_profile_bounds_actual_closed_read_and_filtered_makeNode=True,filter_length_and_residency_retained=True,original_arbitrary_guard_predicate_preserved=True,mu_and_type_skips_keep_heap=True,low_level_actual_done_observer=True,arbitrary_failed_fuel_heap_claimed=False,prefix_producer_derives_common_sufficient_fuel=True,entire_old_prefix_output_retained=True,entire_old_callback_output_retained=True,old_output_contracts=contracts,prefix_uses_same_actual_narrowed_caller=True,native_domains_unchanged=True,empty_rejection_retains_allocations_and_resources=True,empty_rejection_has_no_safe_packet=True,retained_cache_has_packet_at_own_native_endpoint=True,full_Post_memo_witness_retained=True,query_equality_used_as_full_memo_identity=False,callback_native_caller_and_memos_unchanged=True,common_fuel_covers_actual_callback_and_next_accepted_prefix=True,callback_producer_called_once=True,future_success_or_endpoint_capacity_required=False,final_Room_claimed=False,proof_only_finish_executed_by_recursive_worker=False,recursive_subtree_execution_proved=False,hooked_sibling_scan_execution_proved=False,legacy_later_receipts_used_as_hooked_receipts=False,whole_recursive_capacity_proved=False,whole_driver_language_proved=False,host64_capacity_claimed=False,concrete_solver_or_Haskell_correspondence_proved=False)
(area/'source-boundaries.json').write_text(json.dumps(boundaries,indent=2)+'\n')
verification=dict(base=base,source_head=git('rev-parse','HEAD').decode().strip(),recorded_main=main,checks=checks,final_strict_modules=finals,final_source_sha256={rel:sha((root/rel).read_bytes()) for rel in sources},unchanged_source_sha256=unchanged,boundaries=boundaries,public_declarations=len(decls),public_lines=len(text.splitlines()),public_bytes=len(public),public_sha256=sha(public),full_definitions=defs,audit_dependencies=77331,aggregate_jobs=3825,goal_status='active')
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
