import hashlib
import json
import shutil
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]

def write(name, value):
    (HERE / name).write_text(json.dumps(value, indent=2) + '\n')

components = json.loads((HERE / 'components.json').read_text())
assert {item['path'] for item in components} == {'gate-cap', 'independent-review'}
selection = json.loads((HERE / 'gate-cap/gate-cap-selection.json').read_text())
name = 'lean/MicroCFTA/SourceCurrentOriginalGateProjectionCap.lean'
digest = hashlib.sha256((ROOT / name).read_bytes()).hexdigest()
assert digest == selection['source_sha256'] == 'f3b753ade1441826748505f13901964ffb44fe432a8999a34c487932f45055f5'
write('selected-sources.json', {name: {'sha256': digest}})
write('frozen-modules.json', {Path(name).stem: digest})
write('selected-checks.json', {'strict': 'gate-cap-strict-1', 'audit': 'audit-1', 'public': 'gate-cap/' + selection['selected_public']})
(HERE / 'root-support').mkdir(exist_ok=True)
previous = HERE / 'previous-publication-support'
previous.mkdir()
for pattern in ['mcfta-capped-projection-position-publication.json', 'mcfta-capped-projection-position-final-publication*',
                'mcfta-capped-projection-position-final-push.log', 'mcfta-capped-projection-position-final-remote.txt',
                'mcfta-capped-projection-position-board-readback.json', 'mcfta-capped-projection-position-seal-1.*',
                'mcfta-capped-projection-position-support-1.*']:
    found = [path for path in Path('/tmp').glob(pattern) if path.is_file()]
    assert found, pattern
    for source in found:
        shutil.copyfile(source, previous / source.name)
print(json.dumps({'status': 'PASS', 'components': len(components), 'new_modules': 1}))

