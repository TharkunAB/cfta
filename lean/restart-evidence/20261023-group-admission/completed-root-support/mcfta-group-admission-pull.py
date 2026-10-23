import subprocess
from pathlib import Path
root = Path('/home/tritlo/Code/mcfta')
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip() == '591bda7cd4028ee1ed22770c9974142294c92210'
assert not subprocess.check_output(['git','status','--porcelain'],cwd=root)
command = ['git','-c','url.https://github.com/.insteadOf=git@github.com:',
    '-c','credential.helper=','-c','credential.helper=!/snap/bin/gh auth git-credential',
    'pull','--ff-only']
result = subprocess.run(command,cwd=root,capture_output=True)
Path('/tmp/mcfta-group-admission-initial-pull.log').write_bytes(result.stdout+result.stderr)
assert result.returncode == 0, (result.stdout+result.stderr).decode()
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip() == '591bda7cd4028ee1ed22770c9974142294c92210'
print('PASS fast-forward pull; branch and checkpoint unchanged.')
