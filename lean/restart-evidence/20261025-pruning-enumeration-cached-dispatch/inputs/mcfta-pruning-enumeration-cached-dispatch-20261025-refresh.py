import json, subprocess
from pathlib import Path
root=Path('/home/tritlo/Code/mcfta')
def git(*args):
    return subprocess.check_output(['git', *args],cwd=root,stderr=subprocess.STDOUT).decode()
assert not git('status','--porcelain')
print(git('status','--short','--branch'),end='')
print(git('worktree','list','--porcelain'),end='')
print(git('stash','list','--format=%gd %H %s'),end='')
print(git('-c','url.https://github.com/.insteadOf=git@github.com:', '-c','credential.helper=', '-c','credential.helper=!/snap/bin/gh auth git-credential','pull','--ff-only'),end='')
print(json.dumps({k:git('rev-parse',k).strip() for k in ['HEAD','origin/formalize','origin/main']}))
