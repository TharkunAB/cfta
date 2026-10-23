import subprocess
from pathlib import Path
root = Path('/home/tritlo/Code/mcfta')
expected = 'af73f5d67493168cbab9cdd58cbc625d80585a23'
assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root, text=True).strip() == expected
assert not subprocess.check_output(['git', 'status', '--porcelain'], cwd=root)
command = ['git', '-c', 'url.https://github.com/.insteadOf=git@github.com:',
    '-c', 'credential.helper=', '-c', 'credential.helper=!/snap/bin/gh auth git-credential', 'pull', '--ff-only']
result = subprocess.run(command, cwd=root, capture_output=True)
Path('/tmp/mcfta-stored-node-counter-growth-initial-pull.log').write_bytes(result.stdout + result.stderr)
assert result.returncode == 0, (result.stdout + result.stderr).decode()
assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root, text=True).strip() == expected
print('PASS fast-forward pull; branch and checkpoint unchanged.')
