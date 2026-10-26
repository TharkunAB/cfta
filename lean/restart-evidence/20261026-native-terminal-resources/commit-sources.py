from pathlib import Path
import hashlib,json,subprocess
root=Path('/home/tritlo/Code/mcfta');area=Path('/tmp/mcfta-native-terminal-resources-20261026')
git=lambda *a:subprocess.check_output(['git',*a],cwd=root)
base=(area/'base.txt').read_text().strip()
assert git('branch','--show-current').decode().strip()=='formalize'
for module,check in json.loads((area/'final-strict.json').read_text()).items():
    report=json.loads((area/check/'report.json').read_text());data=(root/'lean/MicroCFTA'/f'{module}.lean').read_bytes()
    assert report['exit_code']==0 and report['source_sha256']==hashlib.sha256(data).hexdigest()
for check in ['aggregate-audit-2','public-final-2']:
    assert json.loads((area/check/'report.json').read_text())['exit_code']==0
groups=[('Identify exact successful terminal prefixes across fuel bounds', ['SourcePruningEnumerationTerminalPrefixUnique']), ('Identify complete successful fold observations across fuel bounds', ['SourcePruningEnumerationFoldUnique']), ('Derive terminal admission from original mixed resources', ['SourcePruningEnumerationTerminalAdmission']), ('Retain original resource bounds through complete terminal execution', ['SourcePruningEnumerationCachedTerminalResources']), ('Retain complete terminal adapter outputs with original resources', ['SourcePruningEnumerationCachedTerminalAdapterResources', 'Audit'])]
partial=git('rev-list','--reverse',base+'..HEAD').decode().splitlines();assert len(partial)==4
commits=[]
for commit,(message,modules) in zip(partial,groups[:4]):
    paths=['lean/MicroCFTA/'+name+'.lean' for name in modules]
    assert set(git('diff-tree','--no-commit-id','--name-only','-r',commit).decode().splitlines())==set(paths)
    assert git('show','-s','--format=%s',commit).decode().strip()==message
    for rel in paths:assert git('show',commit+':'+rel)==(root/rel).read_bytes()
    commits.append(dict(commit=commit,message=message,paths=paths))
message,modules=groups[4];paths=['lean/MicroCFTA/'+name+'.lean' for name in modules]
subprocess.run(['git','add','--',*paths],cwd=root,check=True)
assert set(git('diff','--cached','--name-only').decode().splitlines())==set(paths)
for rel in paths:assert git('show',':'+rel)==(root/rel).read_bytes()
subprocess.run(['git','diff','--cached','--check'],cwd=root,check=True)
subprocess.run(['git','commit','-m',message],cwd=root,check=True)
commit=git('rev-parse','HEAD').decode().strip()
for rel in paths:assert git('show',commit+':'+rel)==(root/rel).read_bytes()
commits.append(dict(commit=commit,message=message,paths=paths))
(area/'source-commits.json').write_text(json.dumps(commits,indent=2)+'\n')
print(json.dumps(commits,indent=2))
