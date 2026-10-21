import hashlib
import json
import shutil
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
components = []
for source, target, verifier in [('mcfta-target-later-heap-position-proof', 'later', 'later-position-verify.py'),
                                 ('mcfta-target-later-position-independent-review', 'independent-review', 'verify.py')]:
    destination = HERE / target
    assert not destination.exists()
    shutil.copytree('/tmp/' + source, destination)
    for mode in [[], ['--live']]:
        subprocess.run(['/usr/bin/python3', str(destination / verifier), '--root', str(ROOT), *mode],
                       cwd='/', check=True, stdout=subprocess.DEVNULL)
    components.append({'path': target, 'verifier': verifier, 'extra': ['--root', str(ROOT)], 'live': True})
def write(name, value):
    (HERE / name).write_text(json.dumps(value, indent=2) + '\n')
write('components.json', components)
name = 'lean/MicroCFTA/SourceCurrentTargetLaterHeapPositivePosition.lean'
digest = hashlib.sha256((ROOT / name).read_bytes()).hexdigest()
write('selected-sources.json', {name: {'sha256': digest}})
write('frozen-modules.json', {Path(name).stem: digest})
write('selected-checks.json', {'strict': 'later-strict-1', 'audit': 'audit-1', 'public': 'later/later-position-public-1'})
(HERE / 'root-support').mkdir()
previous = HERE / 'previous-publication-support'
previous.mkdir()
for pattern in ['mcfta-local-position-transport-publication.json', 'mcfta-local-position-transport-final-publication*',
                'mcfta-local-position-transport-final-push.log', 'mcfta-local-position-transport-final-remote.txt',
                'mcfta-local-position-transport-board-readback.json', 'mcfta-local-position-transport-seal-1.*',
                'mcfta-local-position-transport-support-1.*']:
    found = [path for path in Path('/tmp').glob(pattern) if path.is_file()]
    assert found, pattern
    for source in found:
        shutil.copyfile(source, previous / source.name)
print(json.dumps({'status': 'PASS', 'components': len(components), 'new_modules': 1}))
