import datetime
import hashlib
import json
import subprocess
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-partial-congruence-20261024')
area.mkdir()

def git(*args):
    return subprocess.check_output(['git', *args], cwd=root)

head = git('rev-parse', 'HEAD').decode().strip()
assert head == '51505458d39a58890f837393a338855a5523de57'
assert git('status', '--porcelain=v1', '-uall') == b''
for name, args in {
    'baseline-tree.txt': ['ls-tree', '-r', '-z', 'HEAD'],
    'baseline-refs.txt': ['show-ref'],
    'baseline-worktrees.txt': ['worktree', 'list', '--porcelain'],
    'baseline-stashes.txt': ['stash', 'list', '--format=%gd %H %s'],
    'baseline-main-log.txt': ['log', '-12', '--format=%H %s', 'origin/main'],
}.items():
    (area / name).write_bytes(git(*args))
(area / 'baseline.json').write_text(json.dumps({
    'observed_at': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'head': head,
    'main': git('rev-parse', 'origin/main').decode().strip(),
    'tree_sha256': hashlib.sha256((area / 'baseline-tree.txt').read_bytes()).hexdigest(),
    'tracked_files': len((area / 'baseline-tree.txt').read_bytes().split(b'\0')) - 1,
    'clean': True,
    'scope': 'Partial-render congruence and finite transport after the primitive observer checkpoint.',
}, indent=2) + '\n')
print((area / 'baseline.json').read_text())
