import gzip
import hashlib
import json
import subprocess
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
out = Path('/tmp/mcfta-cached-selection-20261024')
start = 'c841846eba7ab893460375a99a34e1d3f27ee9b0'
def git(*args):
    return subprocess.check_output(['git', *args], cwd=root)
assert git('rev-parse', 'HEAD').decode().strip() == start
assert git('branch', '--show-current').decode().strip() == 'formalize'
assert not git('status', '--porcelain')
out.mkdir()
entries = {}
for raw in git('ls-tree', '-r', '-z', 'HEAD').split(b'\0'):
    if not raw:
        continue
    meta, name = raw.split(b'\t', 1)
    mode, kind, blob = meta.decode().split()
    assert kind == 'blob'
    path = root / name.decode()
    data = path.read_bytes()
    assert hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest() == blob
    assert ('100755' if path.stat().st_mode & 0o111 else '100644') == mode
    entries[name.decode()] = dict(mode=mode, blob=blob, bytes=len(data), sha256=hashlib.sha256(data).hexdigest())
data = (json.dumps(entries, indent=2) + '\n').encode()
(out / 'starting-files.json.gz').write_bytes(gzip.compress(data, mtime=0))
for name, args in [('starting-refs.txt', ['show-ref']), ('starting-stashes.txt', ['stash', 'list']),
                   ('starting-worktrees.txt', ['worktree', 'list', '--porcelain'])]:
    (out / name).write_bytes(git(*args))
(out / 'starting-head.txt').write_text(start + '\n')
backup = 'codex/backup-cached-selection-20261024-0122'
subprocess.run(['git', 'branch', backup, start], cwd=root, check=True)
command = ['git', '-c', 'url.https://github.com/.insteadOf=git@github.com:',
           '-c', 'credential.helper=', '-c', 'credential.helper=!/snap/bin/gh auth git-credential']
result = subprocess.run(command + ['pull', '--ff-only'], cwd=root, capture_output=True)
(out / 'pull.log').write_bytes(result.stdout + result.stderr)
assert result.returncode == 0, (result.stdout + result.stderr).decode()
head = git('rev-parse', 'HEAD').decode().strip()
report = dict(status='PASS', start=start, head=head, baseline_files=len(entries),
              baseline_uncompressed_sha256=hashlib.sha256(data).hexdigest(), backup=backup,
              imported_main=git('rev-parse', 'origin/main').decode().strip(),
              same_branch_head=head == start, clean=not bool(git('status', '--porcelain')))
(out / 'bootstrap-report.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report))
