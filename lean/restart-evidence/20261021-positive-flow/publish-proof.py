import json, os, subprocess
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
files=['lean/MicroCFTA/'+name+'.lean' for name in ['SourceCurrentRequiredForestPositive','Audit']]
def git(*args):
 return subprocess.check_output(['git',*args],cwd=ROOT,text=True)
subprocess.run(['git','diff','--check','--',*files],cwd=ROOT,check=True)
subprocess.run(['git','add','--',*files],cwd=ROOT,check=True)
assert set(git('diff','--cached','--name-only').splitlines())==set(files)
subprocess.run(['git','commit','--quiet','-m','Preserve positive positions through actual selected Required forests'],cwd=ROOT,check=True)
head=git('rev-parse','HEAD').strip()
(HERE/'proof-commit.txt').write_text(head+'\n')
env={**os.environ,'GIT_SSH_COMMAND':'ssh -p 443 -o Hostname=ssh.github.com -o HostKeyAlias=github.com -o StrictHostKeyChecking=yes -o ConnectTimeout=15 -o ConnectionAttempts=1 -o BatchMode=yes -o ServerAliveInterval=10 -o ServerAliveCountMax=2'}
with (HERE/'proof-push.log').open('xb') as log:
 subprocess.run(['timeout','45s','git','push','origin','HEAD:formalize'],cwd=ROOT,env=env,stdout=log,stderr=subprocess.STDOUT,check=True)
remote=subprocess.check_output(['timeout','45s','git','ls-remote','origin','refs/heads/formalize','refs/heads/main'],cwd=ROOT,env=env,text=True)
(HERE/'proof-remote.txt').write_text(remote)
assert head+'\trefs/heads/formalize' in remote
assert '794903b3fbad3becb8b28736fc33463760731fc7\trefs/heads/main' in remote
print(json.dumps({'status':'PASS','proof':head,'remote_equal':True}))
