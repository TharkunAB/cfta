import json
import os
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
name = 'lean/MicroCFTA/Audit.lean'
audit = ROOT / name
line = 'import MicroCFTA.SourceCurrentNativeMaybeMuPositivePositions\n'
marker = '/-!\n# Proof dependency audit\n'
text = audit.read_text()
assert text.endswith(line) and text.count(line) == 1 and text.count(marker) == 1
audit.write_text(text.removesuffix(line).replace(marker, line + marker, 1))
def git(*args):
    return subprocess.check_output(['git', *args], cwd=ROOT, text=True)
subprocess.run(['git', 'diff', '--check', '--', name], cwd=ROOT, check=True)
subprocess.run(['git', 'add', '--', name], cwd=ROOT, check=True)
assert git('diff', '--cached', '--name-only').splitlines() == [name]
subprocess.run(['git', 'commit', '--quiet', '-m', 'Import optional binder positions before the axiom audit'], cwd=ROOT, check=True)
head = git('rev-parse', 'HEAD').strip()
(HERE / 'audit-import-fix-commit.txt').write_text(head + '\n')
env = {**os.environ, 'GIT_SSH_COMMAND': 'ssh -p 443 -o Hostname=ssh.github.com -o HostKeyAlias=github.com -o StrictHostKeyChecking=yes -o ConnectTimeout=15 -o ConnectionAttempts=1 -o BatchMode=yes -o ServerAliveInterval=10 -o ServerAliveCountMax=2'}
with (HERE / 'audit-import-fix-push.log').open('xb') as log:
    subprocess.run(['timeout', '45s', 'git', 'push', 'origin', 'HEAD:formalize'], cwd=ROOT, env=env,
                   stdout=log, stderr=subprocess.STDOUT, check=True)
remote = subprocess.check_output(['timeout', '45s', 'git', 'ls-remote', 'origin', 'refs/heads/formalize', 'refs/heads/main'],
                                 cwd=ROOT, env=env, text=True)
(HERE / 'audit-import-fix-remote.txt').write_text(remote)
assert head + '\trefs/heads/formalize' in remote
assert '794903b3fbad3becb8b28736fc33463760731fc7\trefs/heads/main' in remote
print(json.dumps({'status': 'PASS', 'import_fix': head, 'remote_equal': True}))
