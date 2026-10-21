import hashlib
import json
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
START = '7466f1c9d397d38a0eaa81790c869acfcd5f8b13'


def git(*args):
    return subprocess.check_output(['git', *args], cwd=ROOT)


assert git('rev-parse', 'HEAD').decode().strip() == START
env = dict(__import__('os').environ, GIT_SSH_COMMAND='ssh -p 443 -o Hostname=ssh.github.com -o HostKeyAlias=github.com -o StrictHostKeyChecking=yes -o ConnectTimeout=15 -o ConnectionAttempts=1 -o BatchMode=yes -o ServerAliveInterval=10 -o ServerAliveCountMax=2')
with (HERE/'pull.log').open('xb') as log:
    subprocess.run(['timeout','45s','git','pull','--ff-only'],cwd=ROOT,env=env,check=True,stdout=log,stderr=subprocess.STDOUT)
assert git('rev-parse','HEAD').decode().strip()==START
subprocess.run(['git','branch','codex/backup-outer-done-or-exhausted-20261021-1421',START],cwd=ROOT,check=True)
(HERE/'previous-log-fix-publication.json').write_bytes(Path('/tmp/mcfta-sealed-log-fix-publication.json').read_bytes())
paths = git('ls-tree', '-r', '-z', START).split(b'\0')
baseline = {}
for item in paths:
    if not item:
        continue
    metadata, raw_path = item.split(b'\t', 1)
    mode, kind, blob = metadata.decode().split()
    assert kind == 'blob'
    name = raw_path.decode()
    data = (ROOT / name).read_bytes()
    object_id = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
    if object_id != blob:
        raise AssertionError(name)
    baseline[name] = {'mode': mode, 'blob': blob, 'sha256': hashlib.sha256(data).hexdigest()}
(HERE / 'starting-files.json').write_text(json.dumps(baseline, indent=2) + '\n')
for name, arguments in {
    'starting-head.txt': ('rev-parse', 'HEAD'),
    'starting-main.txt': ('rev-parse', 'origin/main'),
    'starting-stashes.txt': ('stash', 'list', '--format=%gd %H %s'),
    'starting-worktrees.txt': ('worktree', 'list', '--porcelain'),
}.items():
    (HERE / name).write_bytes(git(*arguments))
(HERE / 'previous-publication.json').write_bytes(Path('/tmp/mcfta-outer-local-faults-publication.json').read_bytes())
print(json.dumps({'status': 'PASS', 'baseline_files': len(baseline), 'starting_head': START}))
