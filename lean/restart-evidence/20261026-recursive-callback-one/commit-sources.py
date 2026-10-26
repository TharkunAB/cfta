from pathlib import Path
import hashlib,json,subprocess
root=Path('/home/tritlo/Code/mcfta');area=Path('/tmp/mcfta-recursive-callback-one-20261026')
git=lambda *a:subprocess.check_output(['git',*a],cwd=root)
for script in ['verify-checks.py','contracts.py']:subprocess.run(['python3',str(area/script)],check=True)
assert git('branch','--show-current').decode().strip()=='formalize'
assert git('rev-parse','HEAD').decode().strip()==(area/'base.txt').read_text().strip()
assert not git('diff','--cached','--name-only')
finals=json.loads((area/'final-strict.json').read_text());paths=['lean/MicroCFTA/'+name+'.lean' for name in finals]
assert set(git('diff','--name-only').decode().splitlines())=={'lean/MicroCFTA/Audit.lean'}
assert set(git('ls-files','--others','--exclude-standard').decode().splitlines())==set(paths)-{'lean/MicroCFTA/Audit.lean'}
reviews=['review-suspended-mass.txt','review-callback-effects.txt']
for name in reviews:assert 'CLEAR' in (area/name).read_text()
for module in finals:
 if module=='Audit':continue
 sha=hashlib.sha256((root/'lean/MicroCFTA'/f'{module}.lean').read_bytes()).hexdigest()
 assert any(sha in (area/name).read_text() for name in reviews),module
sources=area/'sources';sources.mkdir();patch=git('diff','--binary','--','lean/MicroCFTA/Audit.lean')
for rel in paths:
 data=(root/rel).read_bytes();(sources/Path(rel).name).write_bytes(data)
 if rel!='lean/MicroCFTA/Audit.lean':
  diff=subprocess.run(['git','diff','--no-index','--binary','--','/dev/null',rel],cwd=root,stdout=subprocess.PIPE,check=False)
  assert diff.returncode==1;patch+=diff.stdout
(area/'proof-change.patch').write_bytes(patch)
context=area/'context';context.mkdir()
for name in ['SourcePruningEnumerationRecursiveCallback','SourcePruningEnumerationRunOneResources','SourcePruningEnumerationHookResources','SourcePruningEnumerationHookCertificates','SourcePruningEnumerationOutcomeResources','SourceCurrentColdFiniteWarmCalls']:
 rel='lean/MicroCFTA/'+name+'.lean';data=(root/rel).read_bytes();assert data==git('show',(area/'base.txt').read_text().strip()+':'+rel)
 (context/(name+'.lean')).write_bytes(data)
groups=[('Bound suspended input mass through actual cache writes',['SourcePruningEnumerationSuspendedMass']),('Execute rendered callbacks with one recursive expansion',['SourcePruningEnumerationCallbackOneResources','SourcePruningEnumerationSubtreeEffects','Audit'])]
commits=[]
for message,modules in groups:
 selected=['lean/MicroCFTA/'+name+'.lean' for name in modules]
 subprocess.run(['git','add','--',*selected],cwd=root,check=True)
 assert set(git('diff','--cached','--name-only').decode().splitlines())==set(selected)
 for rel in selected:assert git('show',':'+rel)==(root/rel).read_bytes()
 subprocess.run(['git','diff','--cached','--check'],cwd=root,check=True)
 subprocess.run(['git','commit','-m',message],cwd=root,check=True)
 head=git('rev-parse','HEAD').decode().strip()
 for rel in selected:assert git('show',head+':'+rel)==(root/rel).read_bytes()
 commits.append(dict(commit=head,message=message,paths=selected))
(area/'source-commits.json').write_text(json.dumps(commits,indent=2)+'\n');print(json.dumps(commits,indent=2))
