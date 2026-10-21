import hashlib
import json
import shutil
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write(name, data):
    (HERE / name).write_text(json.dumps(data, indent=2) + '\n')


components = [
    ('combined', '/tmp/mcfta-delayed-combined-owner', 'combined-owner-verify.py', []),
    ('geometry', '/tmp/mcfta-child-separation-investigation', 'child-separation-verify.py', []),
    ('empty', '/tmp/mcfta-merge-empty-support', 'merge-empty-verify.py', ['--root', str(ROOT)]),
    ('review', '/tmp/mcfta-support-foundations-review', 'review-verify.py', []),
    ('support-plan', '/tmp/mcfta-structural-cache-support-investigation', 'verify.py', []),
]
for name, source, verifier, extra in components:
    destination = HERE / name
    assert not destination.exists()
    shutil.copytree(source, destination)
    for mode in [[], ['--live']]:
        subprocess.run(['/usr/bin/python3', str(destination / verifier), *extra, *mode],
                       cwd='/', check=True, stdout=subprocess.DEVNULL)
write('components.json', [{'path': name, 'verifier': verifier, 'extra': extra, 'live': True}
                          for name, _, verifier, extra in components])
modules = ['SourceCurrentDelayedCombinedOwnerProgress', 'SourceCurrentNormalizedChildSeparation',
           'SourceCurrentMergeEmptySupport']
sources = {'lean/MicroCFTA/' + name + '.lean': {'sha256': sha(ROOT / 'lean/MicroCFTA' / (name + '.lean'))}
           for name in modules}
write('selected-sources.json', sources)
write('frozen-modules.json', {Path(name).stem: entry['sha256'] for name, entry in sources.items()})
write('selected-checks.json', {'strict': ['combined-strict-1', 'geometry-strict-1', 'empty-strict-1'],
    'audit': 'audit-1', 'public': ['combined/combined-owner-public-1',
        'geometry/child-separation-public-1', 'empty/merge-empty-public-1'],
    'prelaunch': 'empty/merge-empty-direct-1.json',
    'prelaunch_reason': 'The user-bus connection failed before the capped worker or Lean started.',
    'runtime_search': 'geometry/child-separation-search-1.json'})
support = HERE / 'root-support'
support.mkdir()
for stem in ['mcfta-support-foundations-baseline-1', 'mcfta-support-foundations-proof-push-1']:
    for suffix in ['json', 'log', 'limits.json', 'peaks.txt', 'source.py', 'usage.json']:
        source = Path('/tmp') / (stem + '.' + suffix)
        assert source.is_file(), source
        shutil.copyfile(source, support / source.name)
previous = HERE / 'previous-publication-support'
previous.mkdir()
for pattern in ['mcfta-selected-owner-publication.json', 'mcfta-selected-owner-final-publication*',
                'mcfta-selected-owner-final-push.log', 'mcfta-selected-owner-final-remote.txt',
                'mcfta-selected-owner-board-readback.json', 'mcfta-selected-owner-seal-1.*',
                'mcfta-selected-owner-support-1.*', 'mcfta-sealed-log-fix-2.*',
                'mcfta-sealed-log-fix-push.log', 'mcfta-sealed-log-fix-publication.json',
                'mcfta-fix-sealed-logs.py']:
    found = [path for path in Path('/tmp').glob(pattern) if path.is_file()]
    assert found, pattern
    for source in found:
        shutil.copyfile(source, previous / source.name)
print(json.dumps({'status': 'PASS', 'components': len(components), 'new_modules': len(sources)}))
