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
assert {'class-corridor', 'independent-review'} <= paths <= {'class-corridor', 'independent-review', 'chronology-plan'}
selection = json.loads((HERE / 'class-corridor/class-corridor-selection.json').read_text())
name = 'lean/MicroCFTA/SourceCurrentClassEndpointCorridors.lean'
digest = hashlib.sha256((ROOT / name).read_bytes()).hexdigest()
assert digest == selection['source_sha256'] == 'bc0701959646a61bee767cf6b80db04b314302d16891efd7aa539ca314eacd84'
write('selected-sources.json', {name: {'sha256': digest}})
write('frozen-modules.json', {Path(name).stem: digest})
write('selected-checks.json', {'strict': 'class-strict-1', 'audit': 'audit-1', 'public': 'class-corridor/' + selection['selected_public']})
(HERE / 'root-support').mkdir(exist_ok=True)
previous = HERE / 'previous-publication-support'
previous.mkdir()
for pattern in ['mcfta-raw-corridor-target-caps-publication.json', 'mcfta-raw-corridor-target-caps-final-publication*',
                'mcfta-raw-corridor-target-caps-final-push.log', 'mcfta-raw-corridor-target-caps-final-remote.txt',
                'mcfta-raw-corridor-target-caps-board-readback.json', 'mcfta-raw-corridor-target-caps-seal-1.*',
                'mcfta-raw-corridor-target-caps-support-1.*']:
    found = [path for path in Path('/tmp').glob(pattern) if path.is_file()]
    assert found, pattern
    for source in found:
        shutil.copyfile(source, previous / source.name)
print(json.dumps({'status': 'PASS', 'components': len(components), 'new_modules': 1}))

