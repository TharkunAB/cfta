import hashlib
import json
import subprocess
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
out = Path('/tmp/mcfta-main-refresh-20261024')
expected = 'd501c53489b4ba9a41fd178c7ccdd0bf530dcde7'
def git(*args):
    return subprocess.check_output(['git', *args], cwd=root)
assert git('rev-parse', 'HEAD').decode().strip() == expected
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
(out / 'starting-files.json').write_text(json.dumps(entries, indent=2) + '\n')
(out / 'starting-refs.txt').write_bytes(git('show-ref'))
(out / 'starting-stashes.txt').write_bytes(git('stash', 'list'))
(out / 'starting-worktrees.txt').write_bytes(git('worktree', 'list', '--porcelain'))
(out / 'starting-head.txt').write_text(expected + '\n')
backup = 'codex/backup-main-refresh-20261024-0033'
subprocess.run(['git', 'branch', backup, expected], cwd=root, check=True)
command = ['git', '-c', 'url.https://github.com/.insteadOf=git@github.com:',
           '-c', 'credential.helper=', '-c', 'credential.helper=!/snap/bin/gh auth git-credential']
result = subprocess.run(command + ['pull', '--ff-only'], cwd=root, capture_output=True)
(out / 'pull.log').write_bytes(result.stdout + result.stderr)
assert result.returncode == 0, (result.stdout + result.stderr).decode()
assert git('rev-parse', 'HEAD').decode().strip() == expected
report = dict(status='PASS', start=expected, baseline_files=len(entries), backup=backup,
              upstream_main=git('rev-parse', 'origin/main').decode().strip(),
              worktree_clean=not bool(git('status', '--porcelain')))
(out / 'fetch-report.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report))
