import gzip
import hashlib
import json
import shutil
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
source = Path('/tmp/mcfta-main-refresh-20261024')
here = root / 'lean/restart-evidence/20261024-main-refresh'
here.mkdir()
data = (source / 'starting-files.json').read_bytes()
(here / 'starting-files.json.gz').write_bytes(gzip.compress(data, mtime=0))
(here / 'baseline.json').write_text(json.dumps({'files': 125997, 'uncompressed_bytes': len(data),
    'uncompressed_sha256': hashlib.sha256(data).hexdigest(), 'encoding': 'gzip JSON'}, indent=2) + '\n')
for path in source.iterdir():
    if path.is_file() and path.name != 'starting-files.json' and path.suffix in ['.json', '.log', '.txt', '.hs']:
        shutil.copyfile(path, here / path.name)
reviews = here / 'reviews'
reviews.mkdir()
for suffix in ['core-review', 'programs-review', 'pruning-review', 'final-review']:
    shutil.copyfile(Path('/tmp/mcfta-main-refresh-20261024-' + suffix + '.md'), reviews / (suffix + '.md'))
inputs = here / 'pruning-inputs'
inputs.mkdir()
for path in Path('/tmp/mcfta-main-refresh-20261024-pruning-inputs').iterdir():
    if path.is_file() and path.suffix in ['.json', '.txt', '.hs', '.py', '.patch', '.md']:
        shutil.copyfile(path, inputs / path.name)
jobs = here / 'completed-root-support'
jobs.mkdir()
for path in Path('/tmp').glob('mcfta-main-refresh-20261024-*'):
    if not path.is_file() or path.name.startswith('mcfta-main-refresh-20261024-archive-1'):
        continue
    if path.suffix in ['.json', '.log', '.txt', '.py', '.hs', '.md']:
        shutil.copyfile(path, jobs / path.name)
previous = here / 'previous-scan-publication'
previous.mkdir()
for suffix in ['support-1', 'seal-1', 'local-publication-1', 'authorized-push-1']:
    stem = 'mcfta-scan-node-counter-growth-' + suffix
    paths = list(Path('/tmp').glob(stem + '.*'))
    assert len(paths) == 6, (stem, paths)
    for path in paths:
        shutil.copyfile(path, previous / path.name)
for name in ['local-publication', 'remote-publication']:
    path = Path('/tmp/mcfta-scan-node-counter-growth-' + name + '.json')
    shutil.copyfile(path, previous / path.name)
queued = here / 'queued-counter-consumer'
queued.mkdir()
for name, path in [('declarations', '/tmp/mcfta-after-scan-counter-declarations'),
                   ('review', '/tmp/mcfta-after-scan-counter-declaration-review')]:
    shutil.copytree(path, queued / name)
shutil.copyfile('/tmp/mcfta-main-refresh-20261024-verify-preservation.py', here / 'verify-preservation.py')
files = {}
for path in sorted(here.rglob('*')):
    if path.is_file():
        files[str(path.relative_to(here))] = {'bytes': path.stat().st_size,
                                             'sha256': hashlib.sha256(path.read_bytes()).hexdigest()}
(here / 'artifacts.json').write_text(json.dumps(files, indent=2) + '\n')
print(json.dumps({'status': 'PASS', 'archived_files': len(files), 'baseline_gzip_bytes': (here / 'starting-files.json.gz').stat().st_size,
                  'current_collector_and_later_publication_receipts_remain_outside_this_cut': True}))
