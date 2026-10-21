import hashlib
import json
import shutil
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]

def write(name, value):
    (HERE / name).write_text(json.dumps(value, indent=2) + '\n')

components = json.loads((HERE / 'components.json').read_text())
paths = {item['path'] for item in components}
assert {'projection', 'independent-review'} <= paths <= {'projection', 'independent-review', 'unrestricted-barrier'}
selection = json.loads((HERE / 'projection/capped-position-selection.json').read_text())
name = 'lean/MicroCFTA/SourceCurrentCappedProjectionPositivePosition.lean'
digest = hashlib.sha256((ROOT / name).read_bytes()).hexdigest()
assert digest == selection['source_sha256']
write('selected-sources.json', {name: {'sha256': digest}})
write('frozen-modules.json', {Path(name).stem: digest})
write('selected-checks.json', {'strict': 'projection-strict-1', 'audit': 'audit-1', 'public': 'projection/' + selection['selected_public']})
(HERE / 'root-support').mkdir(exist_ok=True)
previous = HERE / 'previous-publication-support'
previous.mkdir()
for pattern in ['mcfta-native-support-rebase-publication.json', 'mcfta-native-support-rebase-final-publication*',
                'mcfta-native-support-rebase-final-push.log', 'mcfta-native-support-rebase-final-remote.txt',
                'mcfta-native-support-rebase-board-readback.json', 'mcfta-native-support-rebase-seal-1.*',
                'mcfta-native-support-rebase-support-1.*']:
    found = [path for path in Path('/tmp').glob(pattern) if path.is_file()]
    assert found, pattern
    for source in found:
        shutil.copyfile(source, previous / source.name)
print(json.dumps({'status': 'PASS', 'components': len(components), 'new_modules': 1}))

