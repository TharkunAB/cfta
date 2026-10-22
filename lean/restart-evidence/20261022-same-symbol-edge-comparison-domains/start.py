import hashlib
import json
import os
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
START = 'e8a0066c6088d87cc0b0ea9085a07ba2ff44913c'


def git(*args):
    return subprocess.check_output(['git', *args], cwd=ROOT)


assert git('rev-parse', 'HEAD').decode().strip() == START
assert git('branch', '--show-current').decode().strip() == 'formalize'
assert not git('diff', '--name-only') and not git('diff', '--cached', '--name-only')
env = dict(os.environ, GIT_SSH_COMMAND='ssh -p 443 -o Hostname=ssh.github.com -o HostKeyAlias=github.com -o StrictHostKeyChecking=yes -o ConnectTimeout=15 -o ConnectionAttempts=1 -o BatchMode=yes -o ServerAliveInterval=10 -o ServerAliveCountMax=2')
with (HERE / 'pull.log').open('xb') as log:
    subprocess.run(['timeout', '45s', 'git', 'pull', '--ff-only'], cwd=ROOT, env=env,
                   check=True, stdout=log, stderr=subprocess.STDOUT)
assert git('rev-parse', 'HEAD').decode().strip() == START
subprocess.run(['git', 'branch', 'codex/backup-same-symbol-edge-comparison-domains-20261022-0500', START], cwd=ROOT, check=True)
baseline = {}
for item in git('ls-tree', '-r', '-z', START).split(b'\0'):
    if not item:
        continue
    metadata, raw_path = item.split(b'\t', 1)
    mode, kind, blob = metadata.decode().split()
    assert kind == 'blob'
    name = raw_path.decode()
    path = ROOT / name
    assert ('100755' if path.stat().st_mode & 0o111 else '100644') == mode, name
    data = path.read_bytes()
    assert hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest() == blob, name
    baseline[name] = {'mode': mode, 'blob': blob, 'sha256': hashlib.sha256(data).hexdigest()}
(HERE / 'starting-files.json').write_text(json.dumps(baseline, indent=2) + '\n')
for name, arguments in {
    'starting-head.txt': ('rev-parse', 'HEAD'),
    'starting-main.txt': ('rev-parse', 'origin/main'),
    'starting-local-main.txt': ('rev-parse', 'main'),
    'starting-stashes.txt': ('stash', 'list', '--format=%gd %H %s'),
    'starting-worktrees.txt': ('worktree', 'list', '--porcelain'),
}.items():
    (HERE / name).write_bytes(git(*arguments))
(HERE / 'previous-local-checkpoint.json').write_bytes(Path('/tmp/mcfta-same-symbol-edge-comparison-local-publication.json').read_bytes())
print(json.dumps({'status': 'PASS', 'baseline_files': len(baseline), 'starting_head': START}))
