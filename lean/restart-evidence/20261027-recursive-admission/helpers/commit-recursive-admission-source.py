from pathlib import Path
import json
import subprocess
root=Path('/home/tritlo/Code/mcfta'); area=Path('/tmp/mcfta-recursive-admission-20261027')
def git(*args): return subprocess.check_output(['git',*args],cwd=root)
assert git('rev-parse','HEAD').decode().strip()==(area/'published-base.txt').read_text().strip()
assert not git('diff','--cached','--name-only','-z')
modules=json.loads((area/'modules.json').read_text())
groups=[([modules[i] for i in [0,1,2,3,8]],'Retain ordinary invocation and recursive callback admission'),([modules[i] for i in [4,5,6,7]]+['Audit'],'Compose actual selected-step soundness and captured isolation')]
records=[]
for selected,message in groups:
 paths=['lean/MicroCFTA/'+module+'.lean' for module in selected]
 subprocess.run(['git','add','--',*paths],cwd=root,check=True)
 staged={p.decode() for p in git('diff','--cached','--name-only','-z').split(b'\0') if p}
 assert staged==set(paths),staged
 subprocess.run(['git','diff','--cached','--check'],cwd=root,check=True)
 result=subprocess.run(['git','commit','-m',message],cwd=root,check=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 records.append(dict(head=git('rev-parse','HEAD').decode().strip(),message=message,paths=paths,output=result.stdout.decode()))
head=records[-1]['head'];(area/'source-head.txt').write_text(head+'\n');(area/'source-commits.json').write_text(json.dumps(records,indent=2)+'\n')
(area/'source-changes.patch').write_bytes(git('diff','--binary',(area/'published-base.txt').read_text().strip(),head,'--','lean/MicroCFTA'))
print(json.dumps(records))
