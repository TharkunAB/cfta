import hashlib
import json
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
START = '70787b95484cb69897bc4075858e07c7f9c22433'


def git(*args):
    return subprocess.check_output(['git', *args], cwd=ROOT)


assert git('rev-parse', 'HEAD').decode().strip() == START
assert git('branch', '--show-current').decode().strip() == 'formalize'
assert not git('diff', '--name-only') and not git('diff', '--cached', '--name-only')
pull = Path('/tmp/mcfta-original-row-group-chain-initial-pull-1.json')
assert json.loads(pull.read_text())['exit_code'] == 0
(HERE / 'initial-pull-receipt.json').write_bytes(pull.read_bytes())
(HERE / 'pull.log').write_bytes(Path('/tmp/mcfta-original-row-group-chain-initial-pull.log').read_bytes())
assert git('rev-parse', 'HEAD').decode().strip() == START
subprocess.run(['git', 'branch', 'codex/backup-original-row-group-chain-20261022-2345', START], cwd=ROOT, check=True)
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
(HERE / 'previous-local-checkpoint.json').write_bytes(Path('/tmp/mcfta-prepend-grouping-local-publication.json').read_bytes())
print(json.dumps({'status': 'PASS', 'baseline_files': len(baseline), 'starting_head': START}))
