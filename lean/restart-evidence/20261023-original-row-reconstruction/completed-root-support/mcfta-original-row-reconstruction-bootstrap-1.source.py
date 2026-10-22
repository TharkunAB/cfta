import datetime,hashlib,json,shutil,subprocess
from pathlib import Path
R=Path('/home/tritlo/Code/mcfta');P=R/'lean/restart-evidence/20261022-original-row-group-chain'
H=R/'lean/restart-evidence/20261023-original-row-reconstruction'
START='87c0eabce252c0017b1c060750c0a06ebd4fe9b3'
def git(*a):return subprocess.check_output(['git',*a],cwd=R)
assert git('rev-parse','HEAD').decode().strip()==START
assert git('branch','--show-current').decode().strip()=='formalize'
assert not git('status','--porcelain')
assert json.loads(Path('/tmp/mcfta-original-row-reconstruction-initial-pull-1.json').read_text())['exit_code']==0
push=json.loads(Path('/tmp/mcfta-original-row-group-chain-authorized-push.json').read_text())
assert push['status']=='PUSHED_AND_REMOTE_VERIFIED' and push['verified_remote_tip']==START
assert not H.exists();H.mkdir()
subprocess.run(['git','branch','codex/backup-original-row-reconstruction-20261023-0035',START],cwd=R,check=True)
baseline={}
for raw in git('ls-tree','-r','-z',START).split(b'\0'):
 if not raw:continue
 meta,name=raw.split(b'\t',1);mode,kind,blob=meta.decode().split();assert kind=='blob'
 name=name.decode();p=R/name;data=p.read_bytes()
 assert ('100755' if p.stat().st_mode&0o111 else '100644')==mode,name
 assert hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==blob,name
 baseline[name]=dict(mode=mode,blob=blob,sha256=hashlib.sha256(data).hexdigest())
(H/'starting-files.json').write_text(json.dumps(baseline,indent=2)+'\n')
for name,args in {'starting-head.txt':('rev-parse','HEAD'),'starting-main.txt':('rev-parse','origin/main'),'starting-local-main.txt':('rev-parse','main'),'starting-stashes.txt':('stash','list','--format=%gd %H %s'),'starting-worktrees.txt':('worktree','list','--porcelain')}.items():(H/name).write_bytes(git(*args))
(H/'initial-pull-receipt.json').write_bytes(Path('/tmp/mcfta-original-row-reconstruction-initial-pull-1.json').read_bytes())
(H/'pull.log').write_bytes(Path('/tmp/mcfta-original-row-reconstruction-initial-pull.log').read_bytes())
for name in ['root-capped-worker.py']:(H/name).write_bytes((P/name).read_bytes())
old=Path('/tmp/mcfta-original-row-group-chain-driver.py').read_text()
new=old.replace('20261022-original-row-group-chain','20261023-original-row-reconstruction')
assert old.count('20261022-original-row-group-chain')==1
(H/'root-driver.py').write_text(new)
Path('/tmp/mcfta-original-row-reconstruction-driver.py').write_text(new)
(H/'archive-extra.py').write_bytes((P/'archive-extra.py').read_bytes())
(H/'archived-components.json').write_text('{}\n')
counts=dict(status='PASS',baseline_files=len(baseline),older_non_audit_lean=sum(p.endswith('.lean') and p.startswith('lean/') and '/restart-evidence/' not in p and p!='lean/MicroCFTA/Audit.lean' for p in baseline),haskell_files=sum(p.endswith(('.hs','.lhs')) and '/restart-evidence/' not in p for p in baseline),starting_head=START,backup='codex/backup-original-row-reconstruction-20261023-0035',observed_at=datetime.datetime.now().astimezone().isoformat())
(H/'baseline-counts.json').write_text(json.dumps(counts,indent=2)+'\n')
(H/'current-progress.md').write_text('# Ordinary original-row reconstruction\n\nThe whole formalization goal is ACTIVE. This checkpoint starts after H22 is pushed and remote-verified at87c0eabce.\nA fresh pull and exact tracked-file/mode baseline pass. No H23 declaration, body or compiler is authorized yet.\nThe next theorem retains H22 and runs raw ordinary makeNode at its same final caller.\nThe target adds result availability, Ordinary, closedness, full packet and physical language iff.\nIt adds no fresh-result width safety, new-source Room, generated-root admission, Mu/full-pass or Haskell refinement claim.\nNo Haskell repair is added. Keep FINDINGS repair index FIRST. No board operation is authorized.\n')
print(json.dumps(counts))
