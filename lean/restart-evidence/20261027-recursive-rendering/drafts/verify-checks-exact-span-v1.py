from pathlib import Path
import hashlib,json,re,subprocess
root=Path('/home/tritlo/Code/mcfta');area=Path('/tmp/mcfta-recursive-rendering-20261027')
git=lambda *a:subprocess.check_output(['git',*a],cwd=root)
sha=lambda d:hashlib.sha256(d).hexdigest()
modules=json.loads((area/'modules.json').read_text());finals=json.loads((area/'final-strict.json').read_text())
for module,check in finals.items():
 data=(root/'lean/MicroCFTA'/(module+'.lean')).read_bytes();report=json.loads((area/check/'report.json').read_text())
 assert report['exit_code']==0 and report['source_sha256']==sha(data)
 assert data==(area/check/'MicroCFTA'/(module+'.lean')).read_bytes()
 assert data.endswith(b'\n') and not data.endswith(b'\n\n') and all(line.rstrip()==line for line in data.splitlines())
 if module!='Audit':assert not (area/check/'raw.log').read_bytes()
for path in area.rglob('report.json'):
 report=json.loads(path.read_text());raw=(path.parent/'raw.log').read_bytes()
 assert report['bytes']==len(raw) and report['sha256']==sha(raw),path
 assert report['cgroup_limits']=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'},path
for path in list(area.glob('install-*/report.json'))+[area/'aggregate-audit-1/report.json',area/'public-final-1/report.json',area/'native-core-main-2/report.json',area/'native-constrained-extract-1/report.json',area/'format-main-1/report.json',area/'native-specftacular-main-1/report.json']:
 assert json.loads(path.read_text())['exit_code']==0,path
raw=(area/'public-final-1/raw.log').read_text();declarations=json.loads((area/'public-declarations.json').read_text());definitions=json.loads((area/'public-definitions.json').read_text())
assert raw.count('depends on axioms:')+raw.count('does not depend on any axioms')==len(declarations)==9
assert len(re.findall(r'^def MicroCFTA\.',raw,re.M))==len(definitions)==4
assert not re.search(r'\b(?:sorryAx|sorry|admit|native_decide)\b',raw)
assert '⋯' not in raw and '...' not in raw
for axioms in re.findall(r'depends on axioms: \[([^\]]*)\]',raw):
 assert set(x.strip() for x in axioms.split(',') if x.strip())<={'propext','Classical.choice','Quot.sound'}
audit=(area/'strict-audit-2/raw.log').read_text();aggregate=(area/'aggregate-audit-1/raw.log').read_text()
count=int(re.search(r'Checked axiom dependencies of (\d+) MicroCFTA theorems',audit).group(1))
jobs=int(re.search(r'Build completed successfully \((\d+) jobs\)',aggregate).group(1))
base=(area/'base.txt').read_text().strip();main=(area/'main.txt').read_text().strip()
changed=set(git('diff','--name-only',base,'--','lean/MicroCFTA').decode().splitlines())
assert changed<={'lean/MicroCFTA/'+m+'.lean' for m in finals}
old=set(git('ls-tree','-r','--name-only',base,'--','lean/MicroCFTA').decode().splitlines())
assert changed&old=={'lean/MicroCFTA/Audit.lean'}
upstream=json.loads((area/'integration/paths.json').read_text())
for path in upstream:
 if path not in ['CONTEXT.md','cfta/CHANGELOG.md']:
  assert (root/path).read_bytes()==git('show',main+':'+path),path
assert set(git('diff','--name-only',base,'--','cfta','cfta-generator','specftacular','specftacular-ghc').decode().splitlines())=={p for p in upstream if p.split('/')[0] in ['cfta','cfta-generator','specftacular','specftacular-ghc']}
for path in ['CONTEXT.md','cfta/CHANGELOG.md']:
 assert (root/path).read_bytes()==(area/'integration'/Path(path).name).read_bytes()
def verify(value,inherited=None):
 if isinstance(value,dict):
  data=inherited
  key=next((k for k in ['path','snapshot'] if isinstance(value.get(k),str) and {'bytes','sha256'}<=value.keys()),None)
  if key:
   path=Path(value[key]);path=path if path.is_absolute() else root/path
   data=path.read_bytes();assert len(data)==value['bytes'] and sha(data)==value['sha256'],path
  elif isinstance(value.get('source'),dict) and {'path','bytes','sha256'}<=value['source'].keys():
   path=Path(value['source']['path']);data=path.read_bytes()
  span=next(((a,b) for a,b in [('first','last'),('start','end'),('first_line','last_line')] if a in value and b in value and ('sha256' in value or 'span_sha256' in value)),None)
  if span:
   assert data is not None,value
   cut=b''.join(data.splitlines(keepends=True)[value[span[0]]-1:value[span[1]]])
   assert sha(cut)==value.get('span_sha256',value.get('sha256')),value
   if 'bytes' in value:assert len(cut)==value['bytes']
  for child in value.values():verify(child,data)
 elif isinstance(value,list):
  for child in value:verify(child,inherited)
for path in list(area.glob('*pins*.json'))+list(area.glob('review-*.json'))+list(area.glob('*inputs.json')):
 verify(json.loads(path.read_text()))
assert sha((root/'lean/MicroCFTA/SourceCurrentColdFiniteWarmCalls.lean').read_bytes())=='e4665b0bb522ec88f1925fe6bc360b76e9e4bdfbe6192210ac708a3097a20cc5'
imports=''.join('import MicroCFTA.'+m+'\n' for m in modules)
assert (root/'lean/MicroCFTA/Audit.lean').read_bytes()==imports.encode()+(area/'audit-before.lean').read_bytes()
reviews='\n'.join(path.read_text() for path in area.glob('review-*.txt'))
for module in modules:
 source=(root/'lean/MicroCFTA'/(module+'.lean')).read_text()
 assert not re.search(r'\b(?:sorry|admit|axiom|native_decide)\b',source)
 assert 'maxHeartbeats' not in source
 assert sha(source.encode()) in reviews,module
oldtext=(root/'lean/MicroCFTA/SourcePruningEnumerationRecursiveCallback.lean').read_text();newtext=(root/'lean/MicroCFTA/SourcePruningEnumerationRecursiveCallbackCanonical.lean').read_text()
def header(s,name):
 a=s.index('theorem '+name+' ');return s[a:s.index(' := by',a)]
oldh=header(oldtext,'callback_complete');newh=header(newtext,'callback_complete_canonical')
oldin,oldout=oldh.split(' :\n',1);newin,newout=newh.split(' :\n',1)
norm=lambda s:' '.join(s.split())
assert norm(newin.replace('theorem callback_complete_canonical','theorem callback_complete').replace('\n    (canonical : Canonical before.core)',''))==norm(oldin)
oldprefix,newprefix='∃ fuel result after,','∃ fuel result after,'
assert norm(oldout).startswith(oldprefix) and norm(newout).startswith(newprefix)
assert norm(newout)[len(newprefix):].strip()=='('+norm(oldout)[len(oldprefix):].strip()+') ∧ Canonical after'
assert newtext[newtext.index(' := by'):].count('callback_complete formulas ')==1
(area/'contract-retention.json').write_text(json.dumps({'producer':'callback_complete','wrapper':'callback_complete_canonical','entire_old_result_conjunction_retained':True,'explicit_added_admission':'Canonical before.core','producer_calls':1,'old_result_sha256':sha(oldout.encode())},indent=2)+'\n')
assert '341 examples, 0 failures' in (area/'native-core-main-2/raw.log').read_text()
assert (area/'native-constrained-extract-1/raw.log').read_bytes()==b'Nothing\n[(5,Node "p" [Node "h" [Node "b" []],Node "b" []])]\nRight True\n'
subprocess.run(['git','merge-base','--is-ancestor',main,'HEAD'],cwd=root,check=True)
summary=dict(strict_sources=len(finals),public_declarations=len(declarations),full_definitions=len(definitions),public_lines=len(raw.splitlines()),public_bytes=len(raw.encode()),public_sha256=sha(raw.encode()),audited_theorems=count,aggregate_jobs=jobs,main=main,h6_unchanged=True,old_proofs_unchanged=True,core_examples=341,core_failures=0,constrained_extract_defect_confirmed=True,haskell_repair_implemented=False)
(area/'verified-checks.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary,indent=2))
