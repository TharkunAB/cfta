from pathlib import Path
import hashlib, json, re, subprocess
root=Path('/home/tritlo/Code/mcfta'); area=Path('/tmp/mcfta-fold-language-20261026')
git=lambda *a: subprocess.check_output(['git',*a],cwd=root)
sha=lambda data:hashlib.sha256(data).hexdigest()
modules=json.loads((area/'modules.json').read_text()); finals=json.loads((area/'final-strict.json').read_text())
for module,check in finals.items():
 data=(root/'lean/MicroCFTA'/(module+'.lean')).read_bytes()
 report=json.loads((area/check/'report.json').read_text())
 assert report['exit_code']==0 and report['source_sha256']==sha(data),module
 assert data==(area/check/'MicroCFTA'/(module+'.lean')).read_bytes(),module
 assert data.endswith(b'\n') and not data.endswith(b'\n\n') and all(line.rstrip()==line for line in data.splitlines()),module
 if module!='Audit':assert (area/check/'raw.log').read_bytes()==b''
for path in area.rglob('report.json'):
 report=json.loads(path.read_text());raw=(path.parent/'raw.log').read_bytes()
 assert report['bytes']==len(raw) and report['sha256']==sha(raw),path
 assert report['cgroup_limits']=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'},path
for path in list(area.glob('install-*/report.json'))+[area/'aggregate-audit-1/report.json',area/'public-final-1/report.json']:
 assert json.loads(path.read_text())['exit_code']==0,path
raw=(area/'public-final-1/raw.log').read_text()
declarations=json.loads((area/'public-declarations.json').read_text());definitions=json.loads((area/'public-definitions.json').read_text())
assert raw.count('depends on axioms:')+raw.count('does not depend on any axioms')==len(declarations)==7
assert len(re.findall(r'^(?:def|structure) MicroCFTA\.',raw,re.M))==len(definitions)==0
assert not re.search(r'\b(?:sorryAx|sorry|admit|native_decide)\b',raw)
assert '⋯' not in raw and '...' not in raw
for axioms in re.findall(r'depends on axioms: \[([^\]]*)\]',raw):
 assert set(x.strip() for x in axioms.split(',') if x.strip())<={'propext','Classical.choice','Quot.sound'}
audit=(area/'strict-audit-1/raw.log').read_text(); aggregate=(area/'aggregate-audit-1/raw.log').read_text()
count=int(re.search(r'Checked axiom dependencies of (\d+) MicroCFTA theorems',audit).group(1))
jobs=int(re.search(r'Build completed successfully \((\d+) jobs\)',aggregate).group(1))
base=(area/'base.txt').read_text().strip(); main=(area/'main.txt').read_text().strip()
assert not git('diff',base,'--','cfta','cfta-generator','specftacular','specftacular-ghc')
changed=set(git('diff','--name-only',base,'--','lean/MicroCFTA').decode().splitlines())
assert changed<={'lean/MicroCFTA/'+m+'.lean' for m in finals}
for path in (area/'context').glob('*.lean'):
 assert path.read_bytes()==(root/'lean/MicroCFTA'/path.name).read_bytes()==git('show',base+':lean/MicroCFTA/'+path.name)
assert sha((root/'lean/MicroCFTA/SourceCurrentColdFiniteWarmCalls.lean').read_bytes())=='e4665b0bb522ec88f1925fe6bc360b76e9e4bdfbe6192210ac708a3097a20cc5'
imports=''.join('import MicroCFTA.'+m+'\n' for m in modules)
assert (root/'lean/MicroCFTA/Audit.lean').read_bytes()==imports.encode()+(area/'audit-before.lean').read_bytes()
contracts=[]
for old_module,producer,new_module,wrapper in [
 ('SourcePruningEnumerationFold','run_complete','SourcePruningEnumerationFoldLanguage','run_complete_semantics'),
 ('SourcePruningEnumerationTerminal','run_complete','SourcePruningEnumerationTerminalLanguage','run_complete_semantics')]:
 old=(root/'lean/MicroCFTA'/(old_module+'.lean')).read_text();new=(root/'lean/MicroCFTA'/(new_module+'.lean')).read_text()
 a=old.index('theorem '+producer+'\n');b=old.index(' := by',a)
 prefix=old[a:b].replace('theorem '+producer,'theorem '+wrapper,1)
 c=new.index('theorem '+wrapper+'\n');d=new.index(' := by',c)
 assert new[c:d].startswith(prefix+' ∧\n'),wrapper
 assert new[d:].count(producer+' ')==1,wrapper
 contracts.append(dict(old_module=old_module,producer=producer,new_module=new_module,wrapper=wrapper,prefix_bytes=len(prefix.encode()),prefix_sha256=sha(prefix.encode()),producer_calls=1))
(area/'contract-retention.json').write_text(json.dumps(contracts,indent=2)+'\n')
old_paths=set(git('ls-tree','-r','--name-only',base,'--','lean/MicroCFTA').decode().splitlines())
assert changed&old_paths=={'lean/MicroCFTA/Audit.lean'}
reviews='\n'.join((area/path).read_text() for path in ['review-packet.txt','review-fold.txt','review-bridges.txt','review-terminal.txt'])
for module in modules:
 source=(root/'lean/MicroCFTA'/(module+'.lean')).read_text()
 assert not re.search(r'\b(?:sorry|admit|axiom|native_decide)\b',source),module
 assert 'maxHeartbeats' not in source,module
 assert sha(source.encode()) in reviews,module
assert 'CLEAR' in reviews
subprocess.run(['git','merge-base','--is-ancestor',main,'HEAD'],cwd=root,check=True)
summary=dict(strict_sources=len(finals),public_declarations=len(declarations),full_definitions=len(definitions),public_lines=len(raw.splitlines()),public_bytes=len(raw.encode()),public_sha256=sha(raw.encode()),audited_theorems=count,aggregate_jobs=jobs,haskell_changed=False,h6_unchanged=True,entire_old_producer_results_retained=len(contracts))
(area/'verified-checks.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary,indent=2))
