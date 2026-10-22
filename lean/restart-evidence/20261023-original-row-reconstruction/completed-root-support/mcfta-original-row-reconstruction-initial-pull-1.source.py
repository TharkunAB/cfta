import json,os,subprocess
from pathlib import Path
R=Path('/home/tritlo/Code/mcfta')
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip()=='87c0eabce252c0017b1c060750c0a06ebd4fe9b3'
assert not subprocess.check_output(['git','status','--porcelain'],cwd=R)
env=dict(os.environ,GIT_SSH_COMMAND='ssh -p 443 -o Hostname=ssh.github.com -o HostKeyAlias=github.com -o StrictHostKeyChecking=yes -o ConnectTimeout=15 -o ConnectionAttempts=1 -o BatchMode=yes')
p=subprocess.run(['git','pull','--ff-only'],cwd=R,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=120)
Path('/tmp/mcfta-original-row-reconstruction-initial-pull.log').write_bytes(p.stdout)
assert p.returncode==0,p.stdout.decode()
head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip()
assert head=='87c0eabce252c0017b1c060750c0a06ebd4fe9b3',head
print(json.dumps(dict(status='PASS',head=head,pull_exit_code=p.returncode)))
