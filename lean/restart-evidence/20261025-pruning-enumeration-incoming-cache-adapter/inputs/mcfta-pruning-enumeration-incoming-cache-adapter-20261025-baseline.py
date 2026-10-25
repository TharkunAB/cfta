import datetime
import hashlib
import json
import subprocess
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-pruning-enumeration-incoming-cache-adapter-20261025')
area.mkdir(exist_ok=True)
def git(*args):
    return subprocess.check_output(['git', *args], cwd=root)
head = git('rev-parse', 'HEAD').decode().strip()
main = git('rev-parse', 'origin/main').decode().strip()
assert head == '8f47b4357751716acb07f384d00e8115112820a3'
assert main == '74250bd889685da436cdbfe32ac4b5a0878ffd09'
assert not git('status', '--porcelain')
git('branch', 'codex/backup-pruning-enumeration-incoming-cache-adapter-20261025-1146', head)
assert git('rev-parse', 'codex/backup-pruning-enumeration-incoming-cache-adapter-20261025-1146').decode().strip() == head
tree = git('ls-tree', '-r', '-z', head)
(area / 'baseline-tree.txt').write_bytes(tree)
for name, args in [('refs', ('for-each-ref', '--format=%(objectname) %(refname)')),
                   ('worktrees', ('worktree', 'list', '--porcelain')),
                   ('stashes', ('stash', 'list', '--format=%gd %H %s'))]:
    (area / ('baseline-' + name + '.txt')).write_bytes(git(*args))
report = dict(observed_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
              head=head, main=main, tracked_files=len([entry for entry in tree.split(b'\0') if entry]),
              tree_sha256=hashlib.sha256(tree).hexdigest(), clean=True, pull='PASS')
(area / 'baseline.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report))
