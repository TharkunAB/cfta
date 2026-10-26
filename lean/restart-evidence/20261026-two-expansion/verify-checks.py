from pathlib import Path
import hashlib,json,re,subprocess
root=Path('/home/tritlo/Code/mcfta'); area=Path('/tmp/mcfta-two-expansion-20261026')
git=lambda *a:subprocess.check_output(['git',*a],cwd=root)
modules=json.loads((area/'modules.json').read_text()); finals=json.loads((area/'final-strict.json').read_text())
for module,check in finals.items():
 data=(root/'lean/MicroCFTA'/(module+'.lean')).read_bytes(); report=json.loads((area/check/'report.json').read_text())
 assert report['exit_code']==0 and report['source_sha256']==hashlib.sha256(data).hexdigest(),module
 assert data==(area/check/'MicroCFTA'/(module+'.lean')).read_bytes(),module
 assert data.endswith(b'\n') and not data.endswith(b'\n\n') and all(line.rstrip()==line for line in data.splitlines()),module
 if module!='Audit': assert (area/check/'raw.log').read_bytes()==b''
for path in area.rglob('report.json'):
 report=json.loads(path.read_text());raw=(path.parent/'raw.log').read_bytes()
 assert report['bytes']==len(raw) and report['sha256']==hashlib.sha256(raw).hexdigest(),path
 assert report['cgroup_limits']=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'},path
for check in ['install-ordinary-resume','install-prefix-forecasts','install-parked-two','install-selected-two','aggregate-audit-1','public-final-1']:
 assert json.loads((area/check/'report.json').read_text())['exit_code']==0,check
raw=(area/'public-final-1/raw.log').read_text(); declarations=json.loads((area/'public-declarations.json').read_text());definitions=json.loads((area/'public-definitions.json').read_text())
assert raw.count('depends on axioms:')+raw.count('does not depend on any axioms')==len(declarations)==25
assert len(re.findall(r'^(?:def|structure) MicroCFTA\.',raw,re.M))==len(definitions)==23
assert not re.search(r'\b(?:sorryAx|sorry|admit|native_decide)\b',raw)
assert '⋯' not in raw and '...' not in raw
for axioms in re.findall(r'depends on axioms: \[([^\]]*)\]',raw):
 assert set(x.strip() for x in axioms.split(',') if x.strip())<={'propext','Classical.choice','Quot.sound'}
assert '77706' in (area/'strict-audit-1/raw.log').read_text()
assert '3886 jobs' in (area/'aggregate-audit-1/raw.log').read_text()
base=(area/'base.txt').read_text().strip();main=(area/'main.txt').read_text().strip()
assert not git('diff',base,'--','cfta','cfta-generator','specftacular','specftacular-ghc')
changed=set(git('diff','--name-only',base,'--','lean/MicroCFTA').decode().splitlines())
assert changed <= {'lean/MicroCFTA/'+m+'.lean' for m in finals}
for path in (area/'context').glob('*.lean'):
 assert path.read_bytes()==(root/'lean/MicroCFTA'/path.name).read_bytes()==git('show',base+':lean/MicroCFTA/'+path.name)
h6=root/'lean/MicroCFTA/SourceCurrentColdFiniteWarmCalls.lean'
assert hashlib.sha256(h6.read_bytes()).hexdigest()=='e4665b0bb522ec88f1925fe6bc360b76e9e4bdfbe6192210ac708a3097a20cc5'
audit=(root/'lean/MicroCFTA/Audit.lean').read_text()
imports=''.join('import MicroCFTA.'+m+'\n' for m in modules)
assert audit.startswith(imports) and audit.removeprefix(imports).encode()==(area/'audit-before.lean').read_bytes()
old=(root/'lean/MicroCFTA/SourcePruningEnumerationOrdinaryOneResources.lean').read_text()
new=(root/'lean/MicroCFTA/SourcePruningEnumerationOrdinaryOneForecastResources.lean').read_text()
oldName='ordinary_one_complete_resources';newName='ordinary_one_complete_forecast'
a=old.index('    ∃ (bound : Nat)');b=old.index(' := by',a);original=old[a:b]
a=new.index('    ∃ (bound : Nat)');b=new.index(' := by',a)
assert new[a:b].startswith(original+' ∧\n') and new[b:].count(oldName+' ')==1
contract={'old':oldName,'new':newName,'entire_conclusion_prefix_bytes':len(original.encode()),'entire_conclusion_prefix_sha256':hashlib.sha256(original.encode()).hexdigest(),'producer_calls':1}
assert contract==json.loads((area/'contract-retention.json').read_text())
# Git compares all pre-existing tracked Lean sources in one operation.
oldPaths=set(git('ls-tree','-r','--name-only',base,'--','lean/MicroCFTA').decode().splitlines())
assert changed & oldPaths == {'lean/MicroCFTA/Audit.lean'}
for module in modules:
 source=(root/'lean/MicroCFTA'/(module+'.lean')).read_text()
 assert not re.search(r'\b(?:sorry|admit|axiom|native_decide)\b',source),module
 assert 'maxHeartbeats' not in source,module
assert 'overlapped' in (area/'check-scheduling.txt').read_text()
review=(area/'review-new-proofs.txt').read_text();assert 'CLEAR' in review
for module in modules:assert hashlib.sha256((root/'lean/MicroCFTA'/(module+'.lean')).read_bytes()).hexdigest() in review
subprocess.run(['git','merge-base','--is-ancestor',main,'HEAD'],cwd=root,check=True)
summary={'strict_sources':len(finals),'public_declarations':len(declarations),'full_definitions':len(definitions),'public_lines':len(raw.splitlines()),'public_bytes':len(raw.encode()),'public_sha256':hashlib.sha256(raw.encode()).hexdigest(),'audited_theorems':77706,'aggregate_jobs':3886,'haskell_changed':False,'h6_unchanged':True,'entire_old_producer_results_retained':1}
(area/'verified-checks.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary,indent=2))
