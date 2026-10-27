from pathlib import Path
import json,subprocess
r=Path('/home/tritlo/Code/mcfta');a=Path('/tmp/mcfta-recursive-history-resources-20261027')
def git(*args):return subprocess.check_output(['git',*args],cwd=r)
assert not git('diff','--cached','--name-only','-z')
ms=json.loads((a/'modules.json').read_text());groups=[(ms[13:16],'Derive finite admitted output histories from original resources'),(ms[16:]+['Audit'],'Preserve original isolated boundaries through finite enumeration')];records=[]
for names,message in groups:
 paths=[f'lean/MicroCFTA/{m}.lean' for m in names]
 subprocess.run(['git','add','--',*paths],cwd=r,check=True)
 staged={p.decode() for p in git('diff','--cached','--name-only','-z').split(b'\0') if p};assert staged==set(paths)
 subprocess.run(['git','diff','--cached','--check'],cwd=r,check=True)
 result=subprocess.run(['git','commit','-m',message],cwd=r,check=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 records.append(dict(head=git('rev-parse','HEAD').decode().strip(),message=message,paths=paths,output=result.stdout.decode()))
(a/'source-head.txt').write_text(records[-1]['head']+'\n');(a/'source-commits.json').write_text(json.dumps(records,indent=2)+'\n')
(a/'source-changes.patch').write_bytes(git('diff','--binary',(a/'published-base.txt').read_text().strip(),records[-1]['head'],'--','lean/MicroCFTA'))
print(json.dumps(records))
