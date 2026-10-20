import json
import os
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
env = dict(os.environ, GIT_SSH_COMMAND='ssh -p 443 -o Hostname=ssh.github.com '
    '-o HostKeyAlias=github.com -o StrictHostKeyChecking=yes -o ConnectTimeout=15 '
    '-o ConnectionAttempts=1 -o BatchMode=yes -o ServerAliveInterval=10 '
    '-o ServerAliveCountMax=2')
head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip()
with (HERE / 'incremental-push.log').open('xb') as output:
    subprocess.run(['timeout', '45s', 'git', 'push', 'origin', 'formalize'], cwd=ROOT,
                   env=env, stdout=output, stderr=subprocess.STDOUT, check=True)
remote = subprocess.check_output(['timeout', '45s', 'git', 'ls-remote', 'origin',
    'refs/heads/formalize', 'refs/heads/main'], cwd=ROOT, env=env, text=True)
(HERE / 'incremental-remote.txt').write_text(remote)
refs = {line.split()[1]: line.split()[0] for line in remote.splitlines()}
assert refs['refs/heads/formalize'] == head
report = {'status': 'PASS', 'proof_commit': head, 'remote': refs}
(HERE / 'incremental-push.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report))
