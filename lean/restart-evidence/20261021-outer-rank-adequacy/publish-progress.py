import datetime
import json
import os
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
PREFIX = str(HERE.relative_to(ROOT)) + '/'


def git(*args):
    return subprocess.check_output(['git', *args], cwd=ROOT, text=True)


assert git('branch', '--show-current').strip() == 'formalize'
assert all(name.startswith(PREFIX) for name in git('diff', '--name-only').splitlines())
assert all(name.startswith(PREFIX) for name in git('diff', '--cached', '--name-only').splitlines())
assert (HERE / 'IN-PROGRESS.md').is_file()
subprocess.run(['git', 'add', '--', PREFIX], cwd=ROOT, check=True)
names = git('diff', '--cached', '--name-only').splitlines()
assert names and all(name.startswith(PREFIX) for name in names)
owned = [str(path.relative_to(ROOT)) for path in HERE.glob('*.py')]
owned.append(str((HERE / 'IN-PROGRESS.md').relative_to(ROOT)))
subprocess.run(['git', 'diff', '--cached', '--check', '--', *owned], cwd=ROOT, check=True)
subprocess.run(['git', 'commit', '--quiet', '-m',
                'Preserve outer fuel adequacy drafts and check evidence'], cwd=ROOT, check=True)
head = git('rev-parse', 'HEAD').strip()
env = dict(os.environ, GIT_SSH_COMMAND='ssh -p 443 -o Hostname=ssh.github.com -o HostKeyAlias=github.com -o StrictHostKeyChecking=yes -o ConnectTimeout=15 -o ConnectionAttempts=1 -o BatchMode=yes -o ServerAliveInterval=10 -o ServerAliveCountMax=2')
with Path('/tmp/mcfta-outer-rank-adequacy-progress-push.log').open('xb') as log:
    subprocess.run(['timeout', '45s', 'git', 'push', 'origin', 'HEAD:formalize'],
                   cwd=ROOT, env=env, stdout=log, stderr=subprocess.STDOUT, check=True)
remote = subprocess.check_output(['timeout', '45s', 'git', 'ls-remote', 'origin',
                                 'refs/heads/formalize', 'refs/heads/main'], cwd=ROOT, env=env, text=True)
Path('/tmp/mcfta-outer-rank-adequacy-progress-remote.txt').write_text(remote)
assert head + '\trefs/heads/formalize' in remote
assert (HERE / 'starting-main.txt').read_text().strip() + '\trefs/heads/main' in remote
result = {'status': 'PASS', 'checkpoint': head, 'remote_equal': True,
          'files': len(names), 'scope': 'In-progress proof evidence only',
          'new_official_proof_claimed': False,
          'observed_at': datetime.datetime.now(datetime.timezone.utc).isoformat()}
Path('/tmp/mcfta-outer-rank-adequacy-progress-publication.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result))
