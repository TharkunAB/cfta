import hashlib,json,os,subprocess
from pathlib import Path
H=Path(__file__).resolve().parent
R=H.parents[2]
selected=json.loads((H/'selected-sources.json').read_text())
checks=json.loads((H/'selected-checks.json').read_text())['strict']
audit=R/'lean/MicroCFTA/Audit.lean'
text=audit.read_text()
marker='/-!\n# Proof dependency audit\n'
assert text.count(marker)==1
for source,entry in selected.items():
    stem=H/checks[source]
    receipt=json.loads(stem.with_suffix('.json').read_text())
    assert receipt['exit_code']==0 and not stem.with_suffix('.log').read_bytes()
    assert hashlib.sha256((R/source).read_bytes()).hexdigest()==entry['sha256']==receipt['sha256']
    line='import MicroCFTA.'+Path(source).stem+'\n'
    assert line not in text
    text=text.replace(marker,line+marker,1)
audit.write_text(text)
files=[*selected,'lean/MicroCFTA/Audit.lean']
def git(*a):return subprocess.check_output(['git',*a],cwd=R,text=True)
subprocess.run(['git','diff','--check','--',*files],cwd=R,check=True)
subprocess.run(['git','add','--',*files],cwd=R,check=True)
assert set(git('diff','--cached','--name-only').splitlines())==set(files)
subprocess.run(['git','commit','--quiet','-m','Derive and retain target caps from actual raw endpoint corridors'],cwd=R,check=True)
head=git('rev-parse','HEAD').strip()
(H/'proof-commit-corridor-cap.txt').write_text(head+'\n')
env={**os.environ,'GIT_SSH_COMMAND':'ssh -p 443 -o Hostname=ssh.github.com -o HostKeyAlias=github.com -o StrictHostKeyChecking=yes -o ConnectTimeout=15 -o ConnectionAttempts=1 -o BatchMode=yes -o ServerAliveInterval=10 -o ServerAliveCountMax=2'}
with (H/'proof-push-corridor-cap.log').open('xb') as log:
    subprocess.run(['timeout','45s','git','push','origin','HEAD:formalize'],cwd=R,env=env,stdout=log,stderr=subprocess.STDOUT,check=True)
remote=subprocess.check_output(['timeout','45s','git','ls-remote','origin','refs/heads/formalize','refs/heads/main'],cwd=R,env=env,text=True)
(H/'proof-remote-corridor-cap.txt').write_text(remote)
assert head+'\trefs/heads/formalize' in remote
assert '794903b3fbad3becb8b28736fc33463760731fc7\trefs/heads/main' in remote
print(json.dumps({'status':'PASS','proof':head,'new_modules':3,'remote_equal':True}))
