from pathlib import Path
import json,os,subprocess
root=Path('/home/tritlo/Code/mcfta')
remote='git@github.com:TharkunAB/cfta.git'
env=dict(os.environ,GIT_SSH_COMMAND='ssh -o ConnectTimeout=15 -o ConnectionAttempts=1 -o BatchMode=yes -o StrictHostKeyChecking=yes -o HostKeyAlias=github.com -o Hostname=ssh.github.com -p 443')
def run(args):
 p=subprocess.run(args,cwd=root,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
 with Path('/tmp/mcfta-flat-pruning-callback-publication.log').open('a') as f:
  f.write(json.dumps(args)+'\n'+p.stdout)
 if p.returncode:raise RuntimeError(p.stdout)
 return p.stdout.strip()
assert run(['git','branch','--show-current'])=='formalize'
assert not run(['git','status','--porcelain'])
head=run(['git','rev-parse','HEAD'])
print('Publishing '+head,flush=True)
print(run(['git','push',remote,'HEAD:refs/heads/formalize']),flush=True)
remote_head=run(['git','ls-remote',remote,'refs/heads/formalize']).split()[0]
run(['git','fetch',remote,'refs/heads/formalize:refs/remotes/origin/formalize'])
tracking=run(['git','rev-parse','origin/formalize'])
assert head==remote_head==tracking
assert not run(['git','status','--porcelain'])
report={'branch':'formalize','head':head,'remote':remote,'remote_head':remote_head,'tracking_head':tracking,'clean':True}
Path('/tmp/mcfta-flat-pruning-callback-publication.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2),flush=True)
