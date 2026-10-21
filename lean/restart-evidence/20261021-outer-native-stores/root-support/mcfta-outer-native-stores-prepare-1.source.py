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
assert {'outer', 'independent-review', 'producer-plan', 'writer-plan'} == paths
config = [
    ('outer', 'outer-native-stores', 'SourceCurrentOuterNativeStores',
     'b9f7f87df92990b460708bd71fb5f56085bc3b28b97c0a0d96ae1e12f6156f46'),
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
for pattern in ['mcfta-general-parent-native-stores-publication.json', 'mcfta-general-parent-native-stores-final-publication*',
                'mcfta-general-parent-native-stores-final-push.log', 'mcfta-general-parent-native-stores-final-remote.txt',
                'mcfta-general-parent-native-stores-board-readback.json', 'mcfta-general-parent-native-stores-seal-1.*',
                'mcfta-general-parent-native-stores-support-1.*']:
    found = [path for path in Path('/tmp').glob(pattern) if path.is_file()]
    assert found, pattern
    for source in found:
        shutil.copyfile(source, previous / source.name)
print(json.dumps({'status': 'PASS', 'components': len(components), 'new_modules': len(config)}))
