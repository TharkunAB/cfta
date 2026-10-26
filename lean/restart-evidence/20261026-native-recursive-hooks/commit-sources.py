from pathlib import Path
import hashlib,json,subprocess
root=Path('/home/tritlo/Code/mcfta'); area=Path('/tmp/mcfta-native-recursive-hooks-20261026')
run=lambda *args:subprocess.check_output(['git',*args],cwd=root)
assert run('branch','--show-current').decode().strip()=='formalize'
assert run('rev-parse','HEAD').decode().strip()==(area/'base.txt').read_text().strip()
assert not run('diff','--cached','--name-only')
groups=[
 ('Prove exact raw results for concrete pruning callbacks',['EnumerationPartialExact','SourcePruningCallbackExact','SourcePruningAfterCallbackExact']),
 ('Separate selected prefixes from ordinary branch scans',['SourcePruningEnumerationSelectedStep','SourcePruningEnumerationSelectedStepCompletion']),
 ('Retain concrete payloads in native ordinary continuations',['SourcePruningEnumerationNativeContinuations','SourcePruningEnumerationNativeOrdinaryContinuations']),
 ('Run concrete callbacks inside recursive native alternatives',['SourcePruningEnumerationRecursive','SourcePruningEnumerationRecursiveEquations','Audit'])]
commits=[]
for message,modules in groups:
 paths=['lean/MicroCFTA/'+name+'.lean' for name in modules]
 subprocess.run(['git','add','--',*paths],cwd=root,check=True)
 assert set(run('diff','--cached','--name-only').decode().splitlines())==set(paths)
 for rel in paths: assert run('show',':'+rel)==(root/rel).read_bytes(),rel
 subprocess.run(['git','diff','--cached','--check'],cwd=root,check=True)
 subprocess.run(['git','commit','-m',message],cwd=root,check=True)
 commit=run('rev-parse','HEAD').decode().strip()
 for rel in paths: assert run('show',commit+':'+rel)==(root/rel).read_bytes(),rel
 commits.append(dict(commit=commit,message=message,paths=paths))
(area/'source-commits.json').write_text(json.dumps(commits,indent=2)+'\n')
print(json.dumps(commits,indent=2))
