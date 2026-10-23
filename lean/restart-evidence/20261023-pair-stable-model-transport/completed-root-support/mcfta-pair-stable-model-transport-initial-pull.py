import json
import subprocess
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
def git(*args):
    return subprocess.check_output(['git', *args], cwd=root, text=True).strip()

before = git('rev-parse', 'HEAD')
assert before == '0d03a28e82f9f3d0b5dfbba16bc919fb16c422cb'
assert git('branch', '--show-current') == 'formalize'
assert not git('status', '--porcelain')
result = subprocess.run(['git', 'pull', '--ff-only'], cwd=root, capture_output=True, text=True)
Path('/tmp/mcfta-pair-stable-model-transport-initial-pull.log').write_text(result.stdout + result.stderr)
assert result.returncode == 0, result.stderr
print(json.dumps(dict(status='PASS', before=before, after=git('rev-parse', 'HEAD'),
    branch=git('branch', '--show-current'), remote=git('rev-parse', 'origin/formalize'))))
