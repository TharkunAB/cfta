import datetime,hashlib,json,subprocess
from pathlib import Path
root=Path('/home/tritlo/Code/mcfta');area=Path('/tmp/mcfta-pruning-native-view-20261024');area.mkdir()
def git(*args):return subprocess.check_output(['git',*args],cwd=root)
head=git('rev-parse','HEAD').decode().strip();main=git('rev-parse','origin/main').decode().strip()
assert head=='4c52896ccff16f4fbf479ac33746b6dbdf438e35' and main=='74250bd889685da436cdbfe32ac4b5a0878ffd09' and not git('status','--porcelain')
tree=git('ls-tree','-r','-z',head);(area/'baseline-tree.txt').write_bytes(tree)
for name,args in [('refs',('for-each-ref','--format=%(objectname) %(refname)')),('worktrees',('worktree','list','--porcelain')),('stashes',('stash','list','--format=%gd %H %s'))]:
 (area/('baseline-'+name+'.txt')).write_bytes(git(*args))
report=dict(observed_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),head=head,main=main,tracked_files=len([x for x in tree.split(b'\0') if x]),tree_sha256=hashlib.sha256(tree).hexdigest(),clean=True,pull='PASS')
(area/'baseline.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report))
