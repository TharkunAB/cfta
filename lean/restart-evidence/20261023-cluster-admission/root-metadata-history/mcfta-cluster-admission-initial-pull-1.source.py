import json
import os
import subprocess
from pathlib import Path
root = Path('/home/tritlo/Code/mcfta')
start = '3a4cda624829e03055496857356d6edc9f0b4d74'
def git(*args):
    return subprocess.check_output(['git', *args], cwd=root, text=True).strip()
assert git('rev-parse', 'HEAD') == start
assert git('branch', '--show-current') == 'formalize' and not git('status', '--porcelain')
before_main = git('rev-parse', 'origin/main')
command = ['git', '-c', 'url.https://github.com/.insteadOf=git@github.com:',
    '-c', 'credential.helper=', '-c', 'credential.helper=!/snap/bin/gh auth git-credential',
    'pull', '--ff-only']
result = subprocess.run(command, cwd=root, env=dict(os.environ, GIT_TERMINAL_PROMPT='0'),
    capture_output=True, text=True, timeout=90)
Path('/tmp/mcfta-cluster-admission-initial-pull.log').write_text(result.stdout + result.stderr)
assert result.returncode == 0, result.stderr
assert git('rev-parse', 'HEAD') == start
print(json.dumps(dict(status='PASS', before=start, after=git('rev-parse', 'HEAD'),
    remote=git('rev-parse', 'origin/formalize'), before_main=before_main,
    after_main=git('rev-parse', 'origin/main'), transport='HTTPS for this command only')))
