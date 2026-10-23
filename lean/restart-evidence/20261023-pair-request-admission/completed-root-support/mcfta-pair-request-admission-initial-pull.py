import json
import os
import subprocess
from pathlib import Path

ROOT = Path('/home/tritlo/Code/mcfta')
def git(*args):
    return subprocess.check_output(['git', *args], cwd=ROOT, text=True).strip()

before = git('rev-parse', 'HEAD')
assert before == '8e9ca779c555994e1b5b6bb207ef664376f90583'
assert git('branch', '--show-current') == 'formalize'
assert not git('status', '--porcelain')
command = ['git', '-c', 'url.https://github.com/.insteadOf=git@github.com:', 'pull', '--ff-only']
result = subprocess.run(command, cwd=ROOT, env=dict(os.environ, GIT_TERMINAL_PROMPT='0'), capture_output=True, text=True)
Path('/tmp/mcfta-pair-request-admission-initial-pull.log').write_text(result.stdout + result.stderr)
assert result.returncode == 0, result.stderr
print(json.dumps(dict(status='PASS', before=before, after=git('rev-parse', 'HEAD'),
    branch=git('branch', '--show-current'), remote=git('rev-parse', 'origin/formalize'),
    fetch_transport='HTTPS for this command only', push_remote_unchanged=git('remote', 'get-url', '--push', 'origin'))))
