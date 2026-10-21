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
assert {'parent', 'independent-review', 'producer-plan', 'plan-review', 'outer-audit'} == paths
config = [
    ('parent', 'parent-native-stores', 'SourceCurrentActualParentNativeStores',
     'f0a01cf4c787c523b29f357b0d6f0917576dce06db0c6daa684b4fee9ed7b75b'),
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
write('selected-checks.json', {**checks, 'audit': 'audit-2'})
previous = HERE / 'previous-publication-support'
previous.mkdir()
for pattern in ['mcfta-actual-parent-selected-certificates-publication.json', 'mcfta-actual-parent-selected-certificates-final-publication*',
                'mcfta-actual-parent-selected-certificates-final-push.log', 'mcfta-actual-parent-selected-certificates-final-remote.txt',
                'mcfta-actual-parent-selected-certificates-board-readback.json', 'mcfta-actual-parent-selected-certificates-seal-1.*',
                'mcfta-actual-parent-selected-certificates-support-1.*']:
    found = [path for path in Path('/tmp').glob(pattern) if path.is_file()]
    assert found, pattern
    for source in found:
        shutil.copyfile(source, previous / source.name)
print(json.dumps({'status': 'PASS', 'components': len(components), 'new_modules': len(config)}))
