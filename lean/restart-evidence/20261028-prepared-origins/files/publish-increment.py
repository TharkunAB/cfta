from pathlib import Path
import subprocess,json,hashlib,datetime,sys
r=Path('/home/tritlo/Code/mcfta');a=Path('/tmp/mcfta-prepared-origins-20261028');label=sys.argv[1]
assert subprocess.check_output(['git','branch','--show-current'],cwd=r,text=True).strip()=='formalize'
assert subprocess.check_output(['git','remote','get-url','origin'],cwd=r,text=True).strip()=='git@github.com:TharkunAB/cfta.git'
assert subprocess.run(['git','diff','--check'],cwd=r).returncode==0
paths=sys.argv[3:]
subprocess.run(['git','add','--',*paths],cwd=r,check=True)
subprocess.run(['git','commit','-m',sys.argv[2],'--',*paths],cwd=r,check=True)
head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=r,text=True).strip()
(a/(label+'-commit.json')).write_text(json.dumps(dict(head=head,paths=paths,message=sys.argv[2],at=datetime.datetime.now().astimezone().isoformat()),indent=2)+'\n')
print(head)
