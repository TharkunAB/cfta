from pathlib import Path
import hashlib,json,subprocess
root=Path('/home/tritlo/Code/mcfta');area=Path('/tmp/mcfta-enumeration-one-expansion-20261026')
subprocess.run(['python3',str(area/'verify-checks.py')],check=True)
git=lambda *a:subprocess.check_output(['git',*a],cwd=root)
assert git('branch','--show-current').decode().strip()=='formalize'
assert git('rev-parse','HEAD').decode().strip()==(area/'base.txt').read_text().strip()
assert not git('diff','--cached','--name-only')
finals=json.loads((area/'final-strict.json').read_text())
sourcePaths=['lean/MicroCFTA/'+name+'.lean' for name in finals]
assert set(git('diff','--name-only').decode().splitlines())=={'lean/MicroCFTA/Audit.lean'}
assert set(git('ls-files','--others','--exclude-standard').decode().splitlines())==set(sourcePaths)-{'lean/MicroCFTA/Audit.lean'}
reviews=['review-checkpoint-base.txt','review-fallback-finish.txt','review-main-final.txt','review-run-one.txt']
for name in reviews:assert 'CLEAR' in (area/name).read_text()
for module in finals:
    if module=='Audit':continue
    sha=hashlib.sha256((root/'lean/MicroCFTA'/f'{module}.lean').read_bytes()).hexdigest()
    assert any(sha in (area/name).read_text() for name in reviews),module
sources=area/'sources';sources.mkdir()
patch=git('diff','--binary','--','lean/MicroCFTA/Audit.lean')
for rel in sourcePaths:
    data=(root/rel).read_bytes();(sources/Path(rel).name).write_bytes(data)
    if rel!='lean/MicroCFTA/Audit.lean':
        diff=subprocess.run(['git','diff','--no-index','--binary','--','/dev/null',rel],cwd=root,stdout=subprocess.PIPE,check=False)
        assert diff.returncode==1;patch+=diff.stdout
(area/'proof-change.patch').write_bytes(patch)
context=area/'context';context.mkdir()
for rel in ['lean/MicroCFTA/SourcePruningEnumerationSelectedStepCompletion.lean','lean/MicroCFTA/SourcePruningEnumerationRecursive.lean','lean/MicroCFTA/SourcePruningEnumerationOrdinaryForecastResources.lean','lean/MicroCFTA/SourceCurrentColdFiniteWarmCalls.lean']:
    data=(root/rel).read_bytes();assert data==git('show',(area/'base.txt').read_text().strip()+':'+rel)
    (context/Path(rel).name).write_bytes(data)
proposals=area/'proposals';proposals.mkdir()
for path in ['/tmp/mcfta-prefix-execution-proposal/SourcePruningEnumerationPrefixCheckpoint.lean','/tmp/mcfta-parked-one-proposal/SourcePruningEnumerationParkedOneResources.lean','/tmp/mcfta-finish-resources-proposal/SourcePruningEnumerationFinishResources.lean','/tmp/mcfta-resume-execution-proposal/SourcePruningEnumerationResumeExecution.lean','/tmp/mcfta-one-certificates-proposal/SourcePruningEnumerationOutcomeResources.lean','/tmp/mcfta-one-zero-outcome-draft.lean']:
    p=Path(path);(proposals/p.name).write_bytes(p.read_bytes())
(area/'route-inventory.txt').write_bytes(Path('/tmp/mcfta-prefix-route-inventory.txt').read_bytes())
groups=[('Retain resource certificates for actual recursive outcomes',['SourcePruningEnumerationResumeZero','SourcePruningEnumerationOutcomeResources','SourcePruningEnumerationResumeExecution']),('Retain stable selected prefix phases and actual fallback entry',['SourcePruningEnumerationPrefixCheckpoint','SourcePruningEnumerationOrdinaryFallbackResources','SourcePruningEnumerationParkedOneResources']),('Execute one selected expansion under an original reservation',['SourcePruningEnumerationFinishResources','SourcePruningEnumerationOneExpansionResources']),('Derive resource completion for the actual depth-one driver',['SourcePruningEnumerationZeroOutcomeResources','SourcePruningEnumerationRunOneResources','Audit'])]
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
