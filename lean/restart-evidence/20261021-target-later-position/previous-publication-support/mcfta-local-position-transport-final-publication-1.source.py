import hashlib,json,os,subprocess
from pathlib import Path
R=Path('/home/tritlo/Code/mcfta');H=R/'lean/restart-evidence/20261021-local-position-transport'
def git(*a):return subprocess.check_output(['git',*a],cwd=R)
subprocess.run(['/usr/bin/python3',str(H/'verify-seal.py')],check=True)
files=['NEXT-PROMPT.md','HANDOFF.md','FINDINGS.md','lean/README.md','lean/SYSTEM.md','lean/API-COVERAGE.md','lean/COVERAGE.md','lean/notes-proof-status-20261017.md','lean/notes-current-system-claim.md','lean/notes-current-local-position-transport.md']
subprocess.run(['git','diff','--check','--',*files],cwd=R,check=True)
subprocess.run(['git','add','-f','--',*files,str(H.relative_to(R))],cwd=R,check=True)
selected=git('diff','--cached','--name-only').decode().splitlines()
assert all(n in files or n.startswith(str(H.relative_to(R))+'/') for n in selected)
index_names=set(git('ls-files','-z').decode().split('\0'))
sealed_paths=0
for manifest in (R/'lean/restart-evidence').rglob('SHA256SUMS'):
 for line in manifest.read_text().splitlines():
  digest,name=line.split('  ',1)
  p=R/name if name.startswith('lean/') else manifest.parent/name
  relative=str(p.relative_to(R))
  assert relative in index_names,relative
  sealed_paths+=1
subprocess.run(['git','commit','--quiet','-m','Record local positive position laws and remaining native transport'],cwd=R,check=True)
head=git('rev-parse','HEAD').decode().strip()
assert not git('status','--porcelain')
head_entries={}
for raw in git('ls-tree','-r','-z','HEAD').split(b'\0'):
 if not raw:continue
 meta,name=raw.split(b'\t',1);mode,kind,blob=meta.decode().split();assert kind=='blob'
 p=R/name.decode();data=p.read_bytes();assert hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==blob,name
 assert ('100755' if p.stat().st_mode&0o111 else '100644')==mode,name
 head_entries[name.decode()]=(mode,blob)
index={}
for raw in git('ls-files','--stage','-z').split(b'\0'):
 if not raw:continue
 meta,name=raw.split(b'\t',1);mode,blob,stage=meta.decode().split();assert stage=='0';index[name.decode()]=(mode,blob)
assert index==head_entries
subprocess.run(['/usr/bin/python3',str(H/'verify-seal.py')],check=True)
env={**os.environ,'GIT_SSH_COMMAND':'ssh -p 443 -o Hostname=ssh.github.com -o HostKeyAlias=github.com -o StrictHostKeyChecking=yes -o ConnectTimeout=15 -o ConnectionAttempts=1 -o BatchMode=yes -o ServerAliveInterval=10 -o ServerAliveCountMax=2'}
with Path('/tmp/mcfta-local-position-transport-final-push.log').open('xb') as log:
 subprocess.run(['timeout','45s','git','push','origin','HEAD:formalize'],cwd=R,env=env,stdout=log,stderr=subprocess.STDOUT,check=True)
remote=subprocess.check_output(['timeout','45s','git','ls-remote','origin','refs/heads/formalize','refs/heads/main'],cwd=R,env=env,text=True)
Path('/tmp/mcfta-local-position-transport-final-remote.txt').write_text(remote)
assert head+'\trefs/heads/formalize' in remote
assert '794903b3fbad3becb8b28736fc33463760731fc7\trefs/heads/main' in remote
report={'status':'PASS','checkpoint':head,'proofs':{tag:(H/('proof-commit-'+tag+'.txt')).read_text().strip() for tag in ['maybe-mu','target']},'goal_status':'active','filesystem_index_head_equal':True,'tracked_blobs_and_modes':len(index),'all_sealed_paths_in_index':sealed_paths,'clean':not bool(git('status','--porcelain')),'remote':remote,'selected_proof':json.loads((H/'verification.json').read_text()),'preservation':json.loads((H/'preservation-final.json').read_text())}
Path('/tmp/mcfta-local-position-transport-publication.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k not in ['selected_proof','preservation']}))
