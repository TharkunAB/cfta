import json
import os
import subprocess
from pathlib import Path

ROOT = Path('/home/tritlo/Code/mcfta')
def git(*args):
    return subprocess.check_output(['git', *args], cwd=ROOT, text=True).strip()

before = git('rev-parse', 'HEAD')
assert before == '6ca7ff763c6e18d69904b4e860c11f7959eb3d13'
assert git('branch', '--show-current') == 'formalize'
assert not git('status', '--porcelain')
command = ['git', '-c', 'url.https://github.com/.insteadOf=git@github.com:', 'pull', '--ff-only']
result = subprocess.run(command, cwd=ROOT, env=dict(os.environ, GIT_TERMINAL_PROMPT='0'), capture_output=True, text=True, timeout=90)
Path('/tmp/mcfta-both-miss-native-covered-initial-pull.log').write_text(result.stdout + result.stderr)
assert result.returncode == 0, result.stderr
print(json.dumps(dict(status='PASS', before=before, after=git('rev-parse', 'HEAD'),
    branch=git('branch', '--show-current'), remote=git('rev-parse', 'origin/formalize'),
    fetch_transport='HTTPS for this command only', push_remote_unchanged=git('remote', 'get-url', '--push', 'origin'))))
