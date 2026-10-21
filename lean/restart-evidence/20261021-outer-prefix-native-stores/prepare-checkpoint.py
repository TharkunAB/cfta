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
assert {'prefix', 'independent-review', 'writer-plan'} == paths
config = [
    ('prefix', 'prefix-native-stores', 'SourceCurrentOuterPrefixNativeStores',
     '7e1d2349590e0cdd9ad3028e3b25ca1a2d44502766663551fcf901a185a4e1d8'),
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
for pattern in ['mcfta-resource-parent-writers-publication.json', 'mcfta-resource-parent-writers-final-publication*',
                'mcfta-resource-parent-writers-final-push.log', 'mcfta-resource-parent-writers-final-remote.txt',
                'mcfta-resource-parent-writers-board-readback.json', 'mcfta-resource-parent-writers-seal-1.*',
                'mcfta-resource-parent-writers-support-1.*']:
    found = [path for path in Path('/tmp').glob(pattern) if path.is_file()]
    assert found, pattern
    for source in found:
        shutil.copyfile(source, previous / source.name)
print(json.dumps({'status': 'PASS', 'components': len(components), 'new_modules': len(config)}))
