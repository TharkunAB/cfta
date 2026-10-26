from pathlib import Path
import hashlib,json,subprocess
root=Path('/home/tritlo/Code/mcfta');area=Path('/tmp/mcfta-enumeration-original-forecast-20261026')
subprocess.run(['python3',str(area/'verify-checks.py')],check=True)
subprocess.run(['python3',str(area/'contracts.py')],check=True)
git=lambda *a:subprocess.check_output(['git',*a],cwd=root)
assert git('branch','--show-current').decode().strip()=='formalize'
assert git('rev-parse','HEAD').decode().strip()==(area/'base.txt').read_text().strip()
assert not git('diff','--cached','--name-only')
finals=json.loads((area/'final-strict.json').read_text())
sourcePaths=['lean/MicroCFTA/'+name+'.lean' for name in finals]
assert set(git('diff','--name-only').decode().splitlines())=={'lean/MicroCFTA/Audit.lean'}
assert set(git('ls-files','--others','--exclude-standard').decode().splitlines())==set(sourcePaths)-{'lean/MicroCFTA/Audit.lean'}
for name in ['review-forecast.txt','review-prefix.txt','review-composition.txt']:
    review=(area/name).read_text(); assert 'CLEAR' in review
    for module,check in finals.items():
        data=(root/'lean/MicroCFTA'/f'{module}.lean').read_bytes();sha=hashlib.sha256(data).hexdigest()
        if module in ['SourcePruningEnumerationGuardWidth','SourcePruningEnumerationCostBounds','SourcePruningEnumerationOriginalForecast','SourcePruningEnumerationOrdinaryForecastResources'] and name=='review-forecast.txt':assert sha in review
        if module in ['SourcePruningEnumerationPrefixAdmission','SourcePruningEnumerationExpansionAdmission'] and name in ['review-prefix.txt','review-composition.txt']:assert sha in review
sources=area/'sources';sources.mkdir()
patch=git('diff','--binary','--','lean/MicroCFTA/Audit.lean')
for rel in sourcePaths:
    data=(root/rel).read_bytes();(sources/Path(rel).name).write_bytes(data)
    if rel!='lean/MicroCFTA/Audit.lean':
        diff=subprocess.run(['git','diff','--no-index','--binary','--','/dev/null',rel],cwd=root,stdout=subprocess.PIPE,check=False)
        assert diff.returncode==1;patch+=diff.stdout
(area/'proof-change.patch').write_bytes(patch)
context=area/'context';context.mkdir()
for rel in ['lean/MicroCFTA/SourcePruningEnumerationOrdinaryHookResources.lean','lean/MicroCFTA/SourcePruningEnumerationPrefixResources.lean','lean/MicroCFTA/SourceCurrentColdFiniteWarmCalls.lean']:
    data=(root/rel).read_bytes();assert data==git('show',(area/'base.txt').read_text().strip()+':'+rel)
    (context/Path(rel).name).write_bytes(data)
proposals=area/'proposals';proposals.mkdir()
for folder,name in [('guard','SourcePruningEnumerationGuardWidth'),('arity','SourcePruningEnumerationCostBounds'),('prefix','SourcePruningEnumerationPrefixAdmission')]:
    (proposals/(name+'.lean')).write_bytes(Path('/tmp/mcfta-expansion-'+folder+'-proposal') .joinpath(name+'.lean').read_bytes())
groups=[('Bound native alternative costs from original heap and guard inputs',['SourcePruningEnumerationGuardWidth','SourcePruningEnumerationCostBounds','SourcePruningEnumerationOriginalForecast']),('Derive scan reservations from the original selected prefix',['SourcePruningEnumerationPrefixAdmission','SourcePruningEnumerationExpansionAdmission']),('Admit callback-aware ordinary scans under the original forecast',['SourcePruningEnumerationOrdinaryForecastResources','Audit'])]
commits=[]
for message,modules in groups:
    paths=['lean/MicroCFTA/'+name+'.lean' for name in modules]
    subprocess.run(['git','add','--',*paths],cwd=root,check=True)
    assert set(git('diff','--cached','--name-only').decode().splitlines())==set(paths)
    for rel in paths:assert git('show',':'+rel)==(root/rel).read_bytes()
    subprocess.run(['git','diff','--cached','--check'],cwd=root,check=True)
    subprocess.run(['git','commit','-m',message],cwd=root,check=True)
    commit=git('rev-parse','HEAD').decode().strip()
    for rel in paths:assert git('show',commit+':'+rel)==(root/rel).read_bytes()
    commits.append({'commit':commit,'message':message,'paths':paths})
(area/'source-commits.json').write_text(json.dumps(commits,indent=2)+'\n');print(json.dumps(commits,indent=2))
