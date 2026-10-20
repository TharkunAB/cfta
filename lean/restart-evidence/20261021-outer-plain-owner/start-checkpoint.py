import hashlib
import json
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
START = 'b514e9409548df91f95f81ebf32455c45e77b95c'


def git(*args):
    return subprocess.check_output(['git', *args], cwd=ROOT)


assert git('rev-parse', 'HEAD').decode().strip() == START
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
        data = git('show', START + ':' + name)
    baseline[name] = {'mode': mode, 'blob': blob, 'sha256': hashlib.sha256(data).hexdigest()}
(HERE / 'starting-files.json').write_text(json.dumps(baseline, indent=2) + '\n')
for name, arguments in {
    'starting-head.txt': ('rev-parse', 'HEAD'),
    'starting-main.txt': ('rev-parse', 'origin/main'),
    'starting-stashes.txt': ('stash', 'list', '--format=%gd %H %s'),
    'starting-worktrees.txt': ('worktree', 'list', '--porcelain'),
}.items():
    (HERE / name).write_bytes(git(*arguments))
(HERE / 'previous-publication.json').write_bytes(Path('/tmp/mcfta-warm-publication.json').read_bytes())
print(json.dumps({'status': 'PASS', 'baseline_files': len(baseline), 'starting_head': START}))
