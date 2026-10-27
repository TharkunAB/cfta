from pathlib import Path
import hashlib,json,re,subprocess
root=Path('/home/tritlo/Code/mcfta');area=Path('/tmp/mcfta-native-captured-frame-20261027')
git=lambda *a:subprocess.check_output(['git',*a],cwd=root)
sha=lambda data:hashlib.sha256(data).hexdigest()
modules=json.loads((area/'modules.json').read_text());finals=json.loads((area/'final-strict.json').read_text())
for module,check in finals.items():
 data=(root/'lean/MicroCFTA'/(module+'.lean')).read_bytes();report=json.loads((area/check/'report.json').read_text())
 assert report['exit_code']==0 and report['source_sha256']==sha(data),module
 assert data==(area/check/'MicroCFTA'/(module+'.lean')).read_bytes(),module
 assert data.endswith(b'\n') and not data.endswith(b'\n\n') and all(line.rstrip()==line for line in data.splitlines()),module
 if module!='Audit':assert not (area/check/'raw.log').read_bytes()
for path in area.rglob('report.json'):
 report=json.loads(path.read_text());raw=(path.parent/'raw.log').read_bytes()
 assert report['bytes']==len(raw) and report['sha256']==sha(raw),path
 assert report['cgroup_limits']=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'},path
for path in list(area.glob('install-*/report.json'))+[area/'aggregate-audit-1/report.json',area/'public-final-1/report.json']:
 assert json.loads(path.read_text())['exit_code']==0,path
raw=(area/'public-final-1/raw.log').read_text();declarations=json.loads((area/'public-declarations.json').read_text());definitions=json.loads((area/'public-definitions.json').read_text())
assert raw.count('depends on axioms:')+raw.count('does not depend on any axioms')==len(declarations)==41
assert len(re.findall(r'^(?:def|structure) MicroCFTA\.',raw,re.M))==len(definitions)==1
assert not re.search(r'\b(?:sorryAx|sorry|admit|native_decide)\b',raw)
assert '⋯' not in raw and '...' not in raw
for axioms in re.findall(r'depends on axioms: \[([^\]]*)\]',raw):
 assert set(x.strip() for x in axioms.split(',') if x.strip())<={'propext','Classical.choice','Quot.sound'}
audit=(area/'strict-audit-1/raw.log').read_text();aggregate=(area/'aggregate-audit-1/raw.log').read_text()
count=int(re.search(r'Checked axiom dependencies of (\d+) MicroCFTA theorems',audit).group(1))
jobs=int(re.search(r'Build completed successfully \((\d+) jobs\)',aggregate).group(1))
base=(area/'base.txt').read_text().strip();main=(area/'main.txt').read_text().strip()
assert not git('diff',base,'--','cfta','cfta-generator','specftacular','specftacular-ghc')
changed=set(git('diff','--name-only',base,'--','lean/MicroCFTA').decode().splitlines())
assert changed<={'lean/MicroCFTA/'+m+'.lean' for m in finals}
for path in (area/'context').glob('*.lean'):
 assert path.read_bytes()==(root/'lean/MicroCFTA'/path.name).read_bytes()==git('show',base+':lean/MicroCFTA/'+path.name)
def verify_pins(value):
 if isinstance(value,dict):
  if {'path','bytes','sha256'}<=value.keys():
   p=Path(value['path']);p=p if p.is_absolute() else root/p;data=p.read_bytes()
   assert len(data)==value['bytes'] and sha(data)==value['sha256'],p
   for cut in value.get('cuts',[]):
    portion=b''.join(data.splitlines(keepends=True)[cut['start']-1:cut['end']])
    assert len(portion)==cut['bytes'] and sha(portion)==cut['sha256'],(p,cut)
  for child in value.values():verify_pins(child)
 elif isinstance(value,list):
  for child in value:verify_pins(child)
for path in list(area.glob('*pins*.json'))+list((area/'drafts').glob('*pins*.json')):
 verify_pins(json.loads(path.read_text()))
assert sha((root/'lean/MicroCFTA/SourceCurrentColdFiniteWarmCalls.lean').read_bytes())=='e4665b0bb522ec88f1925fe6bc360b76e9e4bdfbe6192210ac708a3097a20cc5'
imports=''.join('import MicroCFTA.'+m+'\n' for m in modules)
assert (root/'lean/MicroCFTA/Audit.lean').read_bytes()==imports.encode()+(area/'audit-before.lean').read_bytes()
contracts=[]
for old_module,producer,new_module,wrapper,added in [
 ('SourcePruningEnumerationIncomingNode','run_complete','SourcePruningEnumerationIncomingNeutralLanguage','run_complete_neutral_semantics',''),
 ('SourcePruningEnumerationDispatch','dispatch_complete','SourcePruningEnumerationDispatchNeutralLanguage','dispatch_complete_neutral_semantics',''),
 ('SourcePruningEnumerationTerminal','run_complete','SourcePruningEnumerationTerminalNeutralLanguage','run_complete_neutral_semantics',''),
 ('SourcePruningEnumerationShallowChild','prepareChild_complete','SourcePruningEnumerationShallowChildNeutralLanguage','prepareChild_complete_neutral_semantics',''),
 ('SourcePruningEnumerationCachedPrepare','complete','SourcePruningEnumerationCachedPrepareNeutralLanguage','complete_neutral_semantics',''),
 ('SourcePruningEnumerationCachedTerminalAdapter','complete','SourcePruningEnumerationCachedTerminalNeutralLanguage','complete_neutral_semantics',''),
 ('SourcePruningEnumerationNativeBranchCompletion','complete_with_history','SourcePruningEnumerationNativeBranchCanonical','complete_with_history_canonical','    (canonical : Canonical before.core)'),
 ('SourcePruningEnumerationNativeOrdinary','complete_with_history','SourcePruningEnumerationNativeOrdinaryCanonical','complete_with_history_canonical','    (canonical : Canonical before.core)')]:
 old=(root/'lean/MicroCFTA'/(old_module+'.lean')).read_text();new=(root/'lean/MicroCFTA'/(new_module+'.lean')).read_text()
 a=old.index('theorem '+producer+'\n');b=old.index(' := by',a);prefix=old[a:b].replace('theorem '+producer,'theorem '+wrapper,1)
 c=new.index('theorem '+wrapper+'\n');d=new.index(' := by',c);actual=new[c:d]
 if added:
  assert actual.count(added)==1
  actual=actual.replace('\n'+added,'',1)
 assert actual.startswith(prefix+' ∧\n'),(wrapper,added)
 assert new[d:].count(producer+' ')==1,wrapper
 contracts.append(dict(old_module=old_module,producer=producer,new_module=new_module,wrapper=wrapper,retained_prefix_bytes=len(prefix.encode()),retained_prefix_sha256=sha(prefix.encode()),explicit_added_admission=added or None,producer_calls=1))
(area/'contract-retention.json').write_text(json.dumps(contracts,indent=2)+'\n')
old_paths=set(git('ls-tree','-r','--name-only',base,'--','lean/MicroCFTA').decode().splitlines())
assert changed&old_paths=={'lean/MicroCFTA/Audit.lean'}
reviews='\n'.join(path.read_text() for path in area.glob('review-*.txt'))
for module in modules:
 source=(root/'lean/MicroCFTA'/(module+'.lean')).read_text()
 assert not re.search(r'\b(?:sorry|admit|axiom|native_decide)\b',source),module
 assert 'maxHeartbeats' not in source,module
 assert sha(source.encode()) in reviews,module
assert 'CLEAR' in reviews
captured=(root/'lean/MicroCFTA/SourcePruningEnumerationCapturedEdgeSoundness.lean').read_text()
assert captured.count('SourcePruningEnumerationSelectedEdge.complete_with_fragments ')==1
assert captured.count('SourcePruningEnumerationFinalize.complete ')==1
assert 'EnumerationFrame.neutralize_restore' in captured and 'initial.annotation_heap' not in captured
subprocess.run(['git','merge-base','--is-ancestor',main,'HEAD'],cwd=root,check=True)
summary=dict(strict_sources=len(finals),public_declarations=len(declarations),full_definitions=len(definitions),public_lines=len(raw.splitlines()),public_bytes=len(raw.encode()),public_sha256=sha(raw.encode()),audited_theorems=count,aggregate_jobs=jobs,haskell_changed=False,h6_unchanged=True,old_sources_unchanged=True,entire_old_producer_results_retained=len(contracts),explicit_canonical_wrapper_admissions=2)
(area/'verified-checks.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary,indent=2))
