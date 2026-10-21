import hashlib
import json
import shutil
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]

def write(name, value):
    (HERE / name).write_text(json.dumps(value, indent=2) + '\n')

components = json.loads((HERE / 'components.json').read_text())
assert {item['path'] for item in components} == {'edge-helper', 'rebase-plan', 'native', 'independent-review'}
name = 'lean/MicroCFTA/SourceCurrentNativeRequestPositivePositions.lean'
digest = hashlib.sha256((ROOT / name).read_bytes()).hexdigest()
assert digest == 'e62eed872e07c2457a0ae577e7e35281b48fe4d5ebc6b90bbb403a62e01c5727'
write('selected-sources.json', {name: {'sha256': digest}})
write('frozen-modules.json', {Path(name).stem: digest})
write('selected-checks.json', {'strict': 'native-strict-1', 'audit': 'audit-1', 'public': 'native/request-position-public-1'})
(HERE / 'root-support').mkdir(exist_ok=True)
previous = HERE / 'previous-publication-support'
previous.mkdir()
for pattern in ['mcfta-target-later-position-publication.json', 'mcfta-target-later-position-final-publication*',
                'mcfta-target-later-position-final-push.log', 'mcfta-target-later-position-final-remote.txt',
                'mcfta-target-later-position-board-readback.json', 'mcfta-target-later-position-seal-1.*',
                'mcfta-target-later-position-support-1.*']:
    found = [path for path in Path('/tmp').glob(pattern) if path.is_file()]
    assert found, pattern
    for source in found:
        shutil.copyfile(source, previous / source.name)
print(json.dumps({'status': 'PASS', 'components': len(components), 'new_modules': 1}))

