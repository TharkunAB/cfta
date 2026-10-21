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
assert {'parent-scan', 'independent-review', 'admission-plan', 'owner-geometry-plan'} == paths
config = [
    ('parent-scan', 'parent-scan-stores', 'SourceCurrentActualParentScanNativeStores',
     'fb94ee44471c161ec6d3c94348b07a38ee52fc3823ac28296c66334dc952e8e0'),
]
sources, frozen, checks = {}, {}, {}
for tag, prefix, module, expected in config:
    selection = json.loads((HERE / tag / (prefix + '-selection.json')).read_text())
    name = 'lean/MicroCFTA/' + module + '.lean'
    digest = hashlib.sha256((ROOT / name).read_bytes()).hexdigest()
    assert digest == selection['source_sha256'] == expected
    sources[name] = {'sha256': digest}
    frozen[module] = digest
    checks[tag] = {'strict': tag + '-strict-1', 'public': tag + '/' + selection['selected_public']}
write('selected-sources.json', sources)
write('frozen-modules.json', frozen)
write('selected-checks.json', {**checks, 'audit': 'audit-1'})
previous = HERE / 'previous-publication-support'
previous.mkdir()
for pattern in ['mcfta-scan-native-stores-publication.json', 'mcfta-scan-native-stores-final-publication*',
                'mcfta-scan-native-stores-final-push.log', 'mcfta-scan-native-stores-final-remote.txt',
                'mcfta-scan-native-stores-board-readback.json', 'mcfta-scan-native-stores-seal-1.*',
                'mcfta-scan-native-stores-support-1.*']:
    found = [path for path in Path('/tmp').glob(pattern) if path.is_file()]
    assert found, pattern
    for source in found:
        shutil.copyfile(source, previous / source.name)
print(json.dumps({'status': 'PASS', 'components': len(components), 'new_modules': len(config)}))
