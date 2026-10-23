import json
import os
import subprocess
from pathlib import Path

ROOT = Path('/home/tritlo/Code/mcfta')
def git(*args):
    return subprocess.check_output(['git', *args], cwd=ROOT, text=True).strip()

before = git('rev-parse', 'HEAD')
assert before == 'd8503f911255e53beb8904dacd7d978349ec7887'
assert git('branch', '--show-current') == 'formalize'
assert not git('status', '--porcelain')
command = ['git', '-c', 'url.https://github.com/.insteadOf=git@github.com:', 'pull', '--ff-only']
result = subprocess.run(command, cwd=ROOT, env=dict(os.environ, GIT_TERMINAL_PROMPT='0'), capture_output=True, text=True, timeout=90)
Path('/tmp/mcfta-completed-hit-readback-initial-pull.log').write_text(result.stdout + result.stderr)
assert result.returncode == 0, result.stderr
print(json.dumps(dict(status='PASS', before=before, after=git('rev-parse', 'HEAD'),
    branch=git('branch', '--show-current'), remote=git('rev-parse', 'origin/formalize'),
    fetch_transport='HTTPS for this command only', push_remote_unchanged=git('remote', 'get-url', '--push', 'origin'))))
