from pathlib import Path
import hashlib, json, subprocess
root=Path('/home/tritlo/Code/mcfta'); area=Path('/tmp/mcfta-native-hook-resources-20261026')
git=lambda *a:subprocess.check_output(['git',*a],cwd=root)
assert git('branch','--show-current').decode().strip()=='formalize'
assert git('rev-parse','HEAD').decode().strip()==(area/'base.txt').read_text().strip()
assert not git('diff','--cached','--name-only')
finals=json.loads((area/'final-strict.json').read_text())
for module,check in finals.items():
    data=(root/'lean/MicroCFTA'/f'{module}.lean').read_bytes()
    report=json.loads((area/check/'report.json').read_text())
    assert report['exit_code']==0 and report['source_sha256']==hashlib.sha256(data).hexdigest()
for check in ['helper-build-1','helper-build-2','helper-build-3','install-hook-1','install-callback-final-1','install-ordinary-final-1','aggregate-audit-1','public-final-1']:
    assert json.loads((area/check/'report.json').read_text())['exit_code']==0
groups=[('Expose the original resource producer for one native alternative', ['SourcePruningEnumerationNativeBranchResources']), ('Certify actual callbacks and continued native heads', ['SourcePruningEnumerationCallbackZero', 'SourcePruningEnumerationContinuationHead']), ('Retain own-endpoint certificates through callback receipts', ['SourcePruningEnumerationHookCertificates', 'SourcePruningEnumerationReceiptHook']), ('Derive original resources for the actual callback-aware scan', ['SourcePruningEnumerationHookResources']), ('Connect ordinary entry to the actual callback-aware scan', ['SourcePruningEnumerationOrdinaryHookResources', 'Audit'])]
commits=[]
for message,modules in groups:
    paths=['lean/MicroCFTA/'+name+'.lean' for name in modules]
    subprocess.run(['git','add','--',*paths],cwd=root,check=True)
    assert set(git('diff','--cached','--name-only').decode().splitlines())==set(paths)
    for rel in paths: assert git('show',':'+rel)==(root/rel).read_bytes()
    subprocess.run(['git','diff','--cached','--check'],cwd=root,check=True)
    subprocess.run(['git','commit','-m',message],cwd=root,check=True)
    commit=git('rev-parse','HEAD').decode().strip()
    for rel in paths: assert git('show',commit+':'+rel)==(root/rel).read_bytes()
    commits.append(dict(commit=commit,message=message,paths=paths))
(area/'source-commits.json').write_text(json.dumps(commits,indent=2)+'\n')
print(json.dumps(commits,indent=2))
