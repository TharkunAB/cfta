import json
import os
import subprocess
from pathlib import Path

ROOT = Path('/home/tritlo/Code/mcfta')
START = 'b796e8e660a73ac328d41cad53c61099ba79d93f'

def git(*args):
    return subprocess.check_output(['git', *args], cwd=ROOT, text=True).strip()

assert git('rev-parse', 'HEAD') == START
assert git('branch', '--show-current') == 'formalize'
assert not git('status', '--porcelain')
before_main = git('rev-parse', 'origin/main')
command = ['git', '-c', 'url.https://github.com/.insteadOf=git@github.com:', 'pull', '--ff-only']
result = subprocess.run(command, cwd=ROOT, env=dict(os.environ, GIT_TERMINAL_PROMPT='0'),
    capture_output=True, text=True, timeout=90)
Path('/tmp/mcfta-comparison-native-covered-initial-pull.log').write_text(result.stdout + result.stderr)
assert result.returncode == 0, result.stderr
assert git('rev-parse', 'HEAD') == START
print(json.dumps(dict(status='PASS', before=START, after=git('rev-parse', 'HEAD'),
    branch=git('branch', '--show-current'), remote=git('rev-parse', 'origin/formalize'),
    before_main=before_main, after_main=git('rev-parse', 'origin/main'),
    fetch_transport='HTTPS for this command only', push_remote_unchanged=git('remote', 'get-url', '--push', 'origin'))))
