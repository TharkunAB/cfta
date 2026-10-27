from pathlib import Path
import json,subprocess
root=Path('/home/tritlo/Code/mcfta')
area=Path('/tmp/mcfta-callback-progress-20261027')
def git(*args):return subprocess.check_output(['git',*args],cwd=root,stderr=subprocess.STDOUT)
assert git('branch','--show-current').decode().strip()=='formalize'
assert git('rev-parse','HEAD').decode().strip()==(area/'published-base.txt').read_text().strip()
assert not git('diff','--cached','--name-only','-z')
commits=[]
for paths,message in [(['lean/MicroCFTA/SourcePruningEnumerationNativeProgress.lean'],'Prove native restart progress from proper pending paths'),(['lean/MicroCFTA/SourcePruningEnumerationCallbackProgress.lean','lean/MicroCFTA/Audit.lean'],'Preserve callback resources and exclude stuck native restart')]:
    git('add','--',*paths)
    staged={p.decode() for p in git('diff','--cached','--name-only','-z').split(b'\0') if p}
    assert staged==set(paths),staged
    git('diff','--cached','--check')
    output=git('commit','-m',message).decode()
    commits.append(dict(head=git('rev-parse','HEAD').decode().strip(),paths=paths,output=output))
(area/'source-head.txt').write_text(commits[-1]['head']+'\n')
(area/'source-commits.json').write_text(json.dumps(commits,indent=2)+'\n')
print(json.dumps(commits))
