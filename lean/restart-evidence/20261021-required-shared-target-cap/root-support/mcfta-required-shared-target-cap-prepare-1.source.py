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
assert paths == {'shared-cap', 'independent-review'}
selection = json.loads((HERE / 'shared-cap/shared-cap-selection.json').read_text())
name = 'lean/MicroCFTA/SourceCurrentRequiredSharedTargetCap.lean'
digest = hashlib.sha256((ROOT / name).read_bytes()).hexdigest()
assert digest == selection['source_sha256'] == 'e6a2c3bb9ce0123877feee3e836770a1ddd24f10a2dd057ef3441feda9bb42cb'
write('selected-sources.json', {name: {'sha256': digest}})
write('frozen-modules.json', {Path(name).stem: digest})
write('selected-checks.json', {'strict': 'shared-strict-1', 'audit': 'audit-1', 'public': 'shared-cap/' + selection['selected_public']})
(HERE / 'root-support').mkdir(exist_ok=True)
previous = HERE / 'previous-publication-support'
previous.mkdir()
for pattern in ['mcfta-required-forest-projection-cap-publication.json', 'mcfta-required-forest-projection-cap-final-publication*',
                'mcfta-required-forest-projection-cap-final-push.log', 'mcfta-required-forest-projection-cap-final-remote.txt',
                'mcfta-required-forest-projection-cap-board-readback.json', 'mcfta-required-forest-projection-cap-seal-1.*',
                'mcfta-required-forest-projection-cap-support-1.*']:
    found = [path for path in Path('/tmp').glob(pattern) if path.is_file()]
    assert found, pattern
    for source in found:
        shutil.copyfile(source, previous / source.name)
print(json.dumps({'status': 'PASS', 'components': len(components), 'new_modules': 1}))

