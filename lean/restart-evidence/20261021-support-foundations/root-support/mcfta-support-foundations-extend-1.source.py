import hashlib
import json
import shutil
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(name):
    return json.loads((HERE / name).read_text())


def write(name, data):
    (HERE / name).write_text(json.dumps(data, indent=2) + '\n')


components = read('components.json')
for name, source, verifier, extra in [
    ('required', '/tmp/mcfta-required-positive-position', 'required-positive-verify.py', ['--root', str(ROOT)]),
    ('required-review', '/tmp/mcfta-required-positive-review', 'review-verify.py', []),
]:
    destination = HERE / name
    assert not destination.exists()
    shutil.copytree(source, destination)
    for mode in [[], ['--live']]:
        subprocess.run(['/usr/bin/python3', str(destination / verifier), *extra, *mode],
                       cwd='/', check=True, stdout=subprocess.DEVNULL)
    components.append({'path': name, 'verifier': verifier, 'extra': extra, 'live': True})
write('components.json', components)
sources = read('selected-sources.json')
name = 'lean/MicroCFTA/SourceCurrentRequiredPositivePosition.lean'
sources[name] = {'sha256': sha(ROOT / name)}
write('selected-sources.json', sources)
write('frozen-modules.json', {Path(name).stem: entry['sha256'] for name, entry in sources.items()})
selected = read('selected-checks.json')
selected['strict'].append('required-strict-1')
selected['audit'] = 'audit-2'
selected['public'].append('required/required-positive-public-1')
selected['unselected_successes'] = ['audit-1']
write('selected-checks.json', selected)
for stem in ['mcfta-support-foundations-archive-1', 'mcfta-support-foundations-verify-1',
             'mcfta-support-foundations-required-push-1']:
    for suffix in ['json', 'log', 'limits.json', 'peaks.txt', 'source.py', 'usage.json']:
        source = Path('/tmp') / (stem + '.' + suffix)
        assert source.is_file(), source
        shutil.copyfile(source, HERE / 'root-support' / source.name)
print(json.dumps({'status': 'PASS', 'components': len(components), 'new_modules': len(sources)}))
