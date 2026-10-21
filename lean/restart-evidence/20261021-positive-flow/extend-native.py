import datetime
import json
import re
import shutil
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
destination = HERE / 'native-boundary'
assert not destination.exists()
shutil.copytree('/tmp/mcfta-positive-native-support-investigation', destination)
for mode in [[], ['--live']]:
    subprocess.run(['/usr/bin/python3', str(destination / 'positive-native-verify.py'),
                    '--root', str(ROOT), *mode], cwd='/', check=True, stdout=subprocess.DEVNULL)
components = json.loads((HERE / 'components.json').read_text())
components.append({'path': 'native-boundary', 'verifier': 'positive-native-verify.py',
                   'extra': ['--root', str(ROOT)], 'live': True})
(HERE / 'components.json').write_text(json.dumps(components, indent=2) + '\n')
checks = json.loads((HERE / 'selected-checks.json').read_text())
checks['constructed_strict'] = 'native-boundary-strict-1'
checks['constructed_source'] = 'native-boundary/positive-native-kernels.lean'
checks['constructed_public'] = 'native-boundary/positive-native-public-1'
(HERE / 'selected-checks.json').write_text(json.dumps(checks, indent=2) + '\n')
for stem in ['mcfta-positive-flow-archive-1', 'mcfta-positive-flow-verify-1']:
    for suffix in ['json', 'log', 'limits.json', 'peaks.txt', 'source.py', 'usage.json']:
        source = Path('/tmp') / (stem + '.' + suffix)
        assert source.is_file(), source
        shutil.copyfile(source, HERE / 'root-support' / source.name)
stamp = datetime.datetime.now().astimezone().strftime('%Y-%m-%d %H:%M %Z')
old = (HERE / 'current-update.md').read_text()
new = re.sub(r'Updated: .*?\.', 'Updated: ' + stamp + '.', old, count=1)
for name in ['NEXT-PROMPT.md', 'HANDOFF.md', 'lean/README.md', 'lean/SYSTEM.md',
             'lean/API-COVERAGE.md', 'lean/COVERAGE.md', 'lean/notes-proof-status-20261017.md',
             'lean/notes-current-system-claim.md']:
    path = ROOT / name
    content = path.read_text()
    assert content.count(old) == 1, name
    path.write_text(content.replace(old, new, 1))
(HERE / 'current-update.md').write_text(new)
old = (HERE / 'findings-update.md').read_text()
new = re.sub(r'Current proof update: .*?\.', 'Current proof update: ' + stamp + '.', old, count=1)
path = ROOT / 'FINDINGS.md'
content = path.read_text()
assert content.count(old) == 1
path.write_text(content.replace(old, new, 1))
(HERE / 'findings-update.md').write_text(new)
path = ROOT / 'lean/notes-current-positive-flow.md'
path.write_text(re.sub(r'Updated: .*?\.', 'Updated: ' + stamp + '.', path.read_text(), count=1))
print(json.dumps({'status': 'PASS', 'components': len(components), 'updated': stamp}))
