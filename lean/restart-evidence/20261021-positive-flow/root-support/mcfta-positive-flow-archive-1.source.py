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


destination = HERE / 'forest'
assert not destination.exists()
shutil.copytree('/tmp/mcfta-required-forest-positive', destination)
for mode in [[], ['--live']]:
    subprocess.run(['/usr/bin/python3', str(destination / 'forest-positive-verify.py'),
                    '--root', str(ROOT), *mode], cwd='/', check=True, stdout=subprocess.DEVNULL)
write('components.json', [{'path': 'forest', 'verifier': 'forest-positive-verify.py',
                          'extra': ['--root', str(ROOT)], 'live': True}])
name = 'lean/MicroCFTA/SourceCurrentRequiredForestPositive.lean'
write('selected-sources.json', {name: {'sha256': sha(ROOT / name)}})
write('frozen-modules.json', {Path(name).stem: sha(ROOT / name)})
write('selected-checks.json', {'strict': 'forest-strict-1', 'audit': 'audit-1',
                             'public': 'forest/forest-positive-public-1'})
support = HERE / 'root-support'
support.mkdir()
for stem in ['mcfta-positive-flow-baseline-1', 'mcfta-positive-flow-proof-push-1']:
    for suffix in ['json', 'log', 'limits.json', 'peaks.txt', 'source.py', 'usage.json']:
        source = Path('/tmp') / (stem + '.' + suffix)
        assert source.is_file(), source
        shutil.copyfile(source, support / source.name)
previous = HERE / 'previous-publication-support'
previous.mkdir()
for pattern in ['mcfta-support-foundations-publication.json', 'mcfta-support-foundations-final-publication*',
                'mcfta-support-foundations-final-push.log', 'mcfta-support-foundations-final-remote.txt',
                'mcfta-support-foundations-board-readback.json', 'mcfta-support-foundations-seal-1.*',
                'mcfta-support-foundations-support-1.*']:
    found = [path for path in Path('/tmp').glob(pattern) if path.is_file()]
    assert found, pattern
    for source in found:
        shutil.copyfile(source, previous / source.name)
print(json.dumps({'status': 'PASS', 'components': 1, 'new_modules': 1}))
