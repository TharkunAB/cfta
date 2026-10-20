import hashlib,json,os,stat,subprocess
from pathlib import Path
root=Path('/home/tritlo/Code/mcfta')
evidence=root/'lean/restart-evidence/20261021-warm-build-row-origins'
def git(*args): return subprocess.check_output(['git',*args],cwd=root)
head=git('rev-parse','HEAD').decode().strip()
assert head.startswith('b514e9409')
assert not git('status','--porcelain')
index={}
for raw in git('ls-files','--stage','-z').split(b'\0'):
 if not raw: continue
 info,name=raw.split(b'\t',1); mode,blob,stage=info.decode().split(); assert stage=='0'
 index[name.decode()]=(mode,blob)
tree={}
for raw in git('ls-tree','-r','-z','HEAD').split(b'\0'):
 if not raw: continue
 info,name=raw.split(b'\t',1); mode,kind,blob=info.decode().split(); assert kind=='blob'
 tree[name.decode()]=(mode,blob)
assert index==tree
for name,(mode,expected) in tree.items():
 p=root/name
 if mode=='120000':
  assert p.is_symlink(); data=os.readlink(p).encode()
 else:
  assert p.is_file(); data=p.read_bytes()
  assert bool(p.stat().st_mode & 0o111)==(mode=='100755'),name
 actual=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
 assert actual==expected,name
subprocess.run(['/usr/bin/python3',str(evidence/'verify-seal.py')],check=True)
env=dict(os.environ,GIT_SSH_COMMAND='ssh -p 443 -o Hostname=ssh.github.com -o HostKeyAlias=github.com -o StrictHostKeyChecking=yes -o ConnectTimeout=15 -o ConnectionAttempts=1 -o BatchMode=yes -o ServerAliveInterval=10 -o ServerAliveCountMax=2')
with Path('/tmp/mcfta-warm-final-push.log').open('xb') as out:
 subprocess.run(['timeout','45s','git','push','origin','formalize'],cwd=root,env=env,stdout=out,stderr=subprocess.STDOUT,check=True)
remote=subprocess.check_output(['timeout','45s','git','ls-remote','origin','refs/heads/formalize','refs/heads/main'],cwd=root,env=env,text=True)
Path('/tmp/mcfta-warm-final-remote.txt').write_text(remote)
refs={line.split()[1]:line.split()[0] for line in remote.splitlines()}
assert refs['refs/heads/formalize']==head
assert refs['refs/heads/main']=='794903b3fbad3becb8b28736fc33463760731fc7'
assert not git('status','--porcelain')
report={'status':'PASS','checkpoint':head,'proof':'6478734b7f7aee02a36d809bf602c971d4b213e5','goal_status':'active','filesystem_index_head_equal':True,'tracked_blobs_and_modes':len(tree),'clean':True,'remote':refs,'selected_proof':json.loads((evidence/'verification.json').read_text()),'preservation':json.loads((evidence/'preservation-final.json').read_text())}
Path('/tmp/mcfta-warm-publication.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k not in ['selected_proof','preservation']}))
