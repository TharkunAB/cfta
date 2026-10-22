import json
import os
import subprocess
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
git = lambda *args: subprocess.check_output(['git',*args],cwd=root,text=True).strip()
assert git('rev-parse','HEAD') == '70787b95484cb69897bc4075858e07c7f9c22433'
assert git('branch','--show-current') == 'formalize' and not git('status','--porcelain')
env = dict(os.environ,GIT_SSH_COMMAND='ssh -p 443 -o Hostname=ssh.github.com -o HostKeyAlias=github.com -o StrictHostKeyChecking=yes -o ConnectTimeout=15 -o ConnectionAttempts=1 -o BatchMode=yes -o ServerAliveInterval=10 -o ServerAliveCountMax=2')
with Path('/tmp/mcfta-original-row-group-chain-initial-pull.log').open('x') as log:
    subprocess.run(['timeout','45s','git','pull','--ff-only'],cwd=root,env=env,check=True,stdout=log,stderr=subprocess.STDOUT)
assert git('rev-parse','HEAD') == '70787b95484cb69897bc4075858e07c7f9c22433'
print(json.dumps(dict(status='PASS',head=git('rev-parse','HEAD'),remote_formalize=git('rev-parse','origin/formalize'),remote_main=git('rev-parse','origin/main'))))
