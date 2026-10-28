from pathlib import Path
import json,subprocess
root=Path('/home/tritlo/Code/mcfta');area=Path('/tmp/mcfta-accepted-prefix-20261028')
assert subprocess.check_output(['git','branch','--show-current'],cwd=root,text=True).strip()=='formalize'
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip()==(area/'published-base.txt').read_text().strip()
assert not subprocess.check_output(['git','diff','--cached','--name-only'],cwd=root)
modules=json.loads((area/'modules.json').read_text())
groups=[('Preserve accepted models through native initialization and narrowing',modules[:4]),('Carry accepted head models into the actual callback restart',[modules[4]]),('Classify native completion and recursive marker outputs',[modules[5],'Audit'])]
records=[]
for title,modules in groups:
 paths=['lean/MicroCFTA/'+m+'.lean' for m in modules]
 subprocess.run(['git','add','--',*paths],cwd=root,check=True)
 subprocess.run(['git','diff','--cached','--check'],cwd=root,check=True)
 staged=subprocess.check_output(['git','diff','--cached','--name-only','-z'],cwd=root).split(b'\0');assert {v.decode() for v in staged if v}==set(paths)
 r=subprocess.run(['git','commit','-m',title],cwd=root,check=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip();records.append(dict(head=head,title=title,paths=paths,output=r.stdout.decode()));print(r.stdout.decode(),end='')
(area/'source-commits.json').write_text(json.dumps(records,indent=2)+'\n');(area/'source-head.txt').write_text(records[-1]['head']+'\n')
