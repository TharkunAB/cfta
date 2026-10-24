import datetime,hashlib,json,subprocess
from pathlib import Path
root=Path('/home/tritlo/Code/mcfta');area=Path('/tmp/mcfta-th-repair-main-20261024');area.mkdir()
baseline='ed89dccbf8242231cde1abf87e52f909cb726470';old_main='c4f7319acf84213fccc8ea389487d4176e4f0b62';main='74250bd889685da436cdbfe32ac4b5a0878ffd09'
def git(*args):return subprocess.check_output(['git',*args],cwd=root)
assert git('rev-parse','HEAD').decode().strip()==baseline and git('rev-parse','origin/main').decode().strip()==main
assert not git('status','--porcelain')
paths=git('diff','--name-only',old_main,main).decode().splitlines()
assert set(paths)=={'cfta-th/CHANGELOG.md','cfta-th/README.md','cfta-th/src/Data/CFTA/TH.hs','cfta-th/test/Spec.hs','docs/generated-node-views.md'}
pins={}
for name in paths:
    data=(root/name).read_bytes();assert data==git('show',baseline+':'+name)==git('show',main+':'+name)
    assert git('ls-tree',baseline,'--',name)==git('ls-tree',main,'--',name)
    pins[name]=dict(bytes=len(data),sha256=hashlib.sha256(data).hexdigest())
(area/'native-source-pins.json').write_text(json.dumps(pins,indent=2)+'\n')
(area/'main-delta.patch').write_bytes(git('diff','--binary',old_main,main))
(area/'main-history.txt').write_bytes(git('log','--format=fuller',old_main+'..'+main))
tree=git('ls-tree','-r','-z',baseline);(area/'baseline-tree.txt').write_bytes(tree)
for name,args in [('refs',('for-each-ref','--format=%(objectname) %(refname)')),('worktrees',('worktree','list','--porcelain')),('stashes',('stash','list','--format=%gd %H %s'))]:
    (area/('baseline-'+name+'.txt')).write_bytes(git(*args))
report=dict(observed_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),head=baseline,old_main=old_main,main=main,tracked_files=len([x for x in tree.split(b'\0') if x]),tree_sha256=hashlib.sha256(tree).hexdigest(),clean=True,pull='PASS',native_paths=len(paths),native_files_equal=True)
(area/'baseline.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report))
