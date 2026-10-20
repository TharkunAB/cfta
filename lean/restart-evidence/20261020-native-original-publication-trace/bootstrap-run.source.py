import hashlib,json,subprocess
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
def git(*a):return subprocess.check_output(['git',*a],cwd=ROOT,text=True)
head=git('rev-parse','HEAD').strip();assert head=='cf36913f01e73dc3a9dc76fbac3e52d7b90823bb'
(HERE/'starting-head.txt').write_text(head+'\n')
files=git('ls-files').splitlines()
pins={n:hashlib.sha256((ROOT/n).read_bytes()).hexdigest() for n in files}
(HERE/'starting-sha256.json').write_text(json.dumps(pins,indent=2)+'\n')
(HERE/'starting-stashes.txt').write_text(git('stash','list','--format=%gd %H %s'))
(HERE/'starting-worktrees.txt').write_text(git('worktree','list','--porcelain'))
print(json.dumps({'status':'PASS','head':head,'baseline_files':len(files),'older_non_audit_sources':sum(n.startswith('lean/MicroCFTA/') and n.endswith('.lean') and n!='lean/MicroCFTA/Audit.lean' for n in files),'haskell':sum(n.endswith('.hs') for n in files),'package_files':sum(n.split('/')[0] in {'cfta','cfta-generator','cfta-ghc','decision-model'} for n in files)}))
