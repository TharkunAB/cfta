import hashlib,json,re,shutil,subprocess
from pathlib import Path
root=Path('/home/tritlo/Code/mcfta'); area=Path('/tmp/mcfta-native-recursive-hooks-20261026')
evidence=root/'lean/restart-evidence/20261026-native-recursive-hooks'
base=(area/'base.txt').read_text().strip(); sha=lambda b:hashlib.sha256(b).hexdigest()
old=lambda rel:subprocess.check_output(['git','show',base+':'+rel],cwd=root)
checks={p.parent.name:json.loads(p.read_text()) for p in sorted(area.glob('*/report.json'))}
finals=json.loads((area/'final-strict.json').read_text())
for module,name in finals.items():
 rel='lean/MicroCFTA/'+module+'.lean'; data=(root/rel).read_bytes()
 assert checks[name]['exit_code']==0 and checks[name]['source_sha256']==sha(data),module
 assert (area/name/'MicroCFTA'/f'{module}.lean').read_bytes()==data,module
 assert subprocess.check_output(['git','show','HEAD:'+rel],cwd=root)==data,rel
for name,report in checks.items():
 raw=(area/name/'raw.log').read_bytes()
 assert len(raw)==report['bytes'] and sha(raw)==report['sha256'],name
 if name.startswith(('helper-build-','aggregate-audit-','public-')):assert not report['exit_code'],name
public_bytes=(area/'public-final-1/raw.log').read_bytes(); public=public_bytes.decode()
assert len(re.findall(r'depends on axioms:|does not depend on any axioms',public))==28
assert '⋯' not in public and '...' not in public
for ax in re.findall(r'depends on axioms:\s*\[([^]]*)\]',public):assert set(re.findall(r'[A-Za-z_.]+',ax))<={'propext','Classical.choice','Quot.sound'}
audit_log=(area/'aggregate-audit-1/raw.log').read_text()
assert 'Checked axiom dependencies of 77042 MicroCFTA theorems.' in audit_log
expected_audit=old('lean/MicroCFTA/Audit.lean').decode().replace('import MicroCFTA.SourcePruningEnumerationNativeContinuations\n','import MicroCFTA.SourcePruningEnumerationNativeContinuations\nimport MicroCFTA.SourcePruningAfterCallbackExact\nimport MicroCFTA.SourcePruningEnumerationRecursiveEquations\n',1)
assert (root/'lean/MicroCFTA/Audit.lean').read_text()==expected_audit
expected_fold=old('lean/MicroCFTA/SourcePruningEnumerationNativeContinuations.lean').decode().replace('variable {width : Nat} {Output Reason : Type}','universe u v\nvariable {width : Nat} {Output : Type u} {Reason : Type v}').replace('inductive HookResult (Output Reason : Type)','inductive HookResult (Output : Type u) (Reason : Type v)').replace('inductive Stop (Reason : Type)','inductive Stop (Reason : Type v)').replace('inductive Result (Output Reason : Type)','inductive Result (Output : Type u) (Reason : Type v)')
assert (root/'lean/MicroCFTA/SourcePruningEnumerationNativeContinuations.lean').read_text()==expected_fold
unchanged=['lean/MicroCFTA/'+m+'.lean' for m in [
'SourcePruningEnumerationSelectedOrdinary','SourcePruningEnumerationSelectedNarrow','SourcePruningEnumerationRecursion','SourcePruningEnumerationNativeBranches','SourcePruningEnumerationNativeBranchCompletion','SourcePruningEnumerationNativeOrdinary','SourcePruningEnumerationCapturedEdge','SourcePruningCallbackCompletion','SourcePruningRecordTypes','SourcePruningEnumerationNativeIndex','SourcePruningEnumerationAfterCallback','SourcePruningEnumerationRestart','EnumerationCompressionFrame','EnumerationPendingOrder','EnumerationPendingReplacement','EnumerationFragmentHistory','EnumerationOrder','EnumerationPureSelection','EnumerationIndexSelection','EnumerationDriver','SourceCurrentColdFiniteWarmCalls']]
unchanged+=['cfta/src/Data/CFTA/'+f for f in ['Enumeration.hs','Interned/Type.hs','Interned/Cache.hs','Interned/Memo.hs','Interned/Operations.hs']]
for rel in unchanged:assert old(rel)==(root/rel).read_bytes(),rel
subprocess.run(['git','diff','--quiet',base,'--','cfta','cfta-generator','*.cabal'],cwd=root,check=True)
main=subprocess.check_output(['git','rev-parse','origin/main'],cwd=root).decode().strip()
subprocess.run(['git','merge-base','--is-ancestor',main,'HEAD'],cwd=root,check=True)
boundaries=json.loads((area/'source-boundaries.json').read_text());assert all(boundaries['checks'].values())
verification=dict(base=base,source_head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=root).decode().strip(),recorded_main=main,checks=checks,final_strict_modules=finals,failed_checks={name:report['exit_code'] for name,report in checks.items() if report['exit_code']},public_declarations=28,public_lines=len(public.splitlines()),public_bytes=len(public_bytes),public_sha256=sha(public_bytes),audit_dependencies=77042,final_source_sha256={'lean/MicroCFTA/'+m+'.lean':sha((root/'lean/MicroCFTA'/f'{m}.lean').read_bytes()) for m in finals},unchanged_source_sha256={rel:sha((root/rel).read_bytes()) for rel in unchanged},source_boundaries=boundaries,goal_status='active',haskell_unchanged=True,continuation_change_is_universe_only=True,recursive_completion_proved=False,whole_driver_language_proved=False)
(area/'verification.json').write_text(json.dumps(verification,indent=2)+'\n')
sources=list(verification['final_source_sha256'])
(area/'proof-change.patch').write_bytes(subprocess.check_output(['git','diff',base,'HEAD','--',*sources],cwd=root))
for rel in sources:
 target=area/'sources'/rel;target.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(root/rel,target)
 if rel in ['lean/MicroCFTA/Audit.lean','lean/MicroCFTA/SourcePruningEnumerationNativeContinuations.lean','lean/MicroCFTA/SourcePruningEnumerationSelectedStep.lean','lean/MicroCFTA/SourcePruningEnumerationSelectedStepCompletion.lean']:
  target=area/'original-sources'/rel;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(old(rel))
(area/'verification-review.txt').write_text('Concrete callback and recursive ordering reviewed against Enumeration.hs:975-1004.\nEach output retains its emission cache and native endpoint.\nNo error row is erased on a Success-only premise. Exact raw callback singleton is proved.\nA missing captured result retains no invented native endpoint.\nConditional sibling equations do not establish recursive completion.\nThe runtime uses uniform work fuel; its initial-input adequacy remains open.\nWhole-driver language and arbitrary lazy forcing remain open.\nAll previous selected-step theorem headers and Valid proposition remain exact.\n')
assert not evidence.exists()
shutil.copytree(area,evidence)
manifest={str(p.relative_to(evidence)):dict(bytes=p.stat().st_size,sha256=sha(p.read_bytes())) for p in sorted(evidence.rglob('*')) if p.is_file()}
(evidence/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps(dict(checks=len(checks),strict=sum(n.startswith('strict-') for n in checks),strict_failed=len(verification['failed_checks']),strict_final_modules=len(finals),public_declarations=28,audit_dependencies=77042,payloads=len(manifest),bytes=sum(x['bytes'] for x in manifest.values()),manifest_sha256=sha((evidence/'manifest.json').read_bytes())),indent=2))
