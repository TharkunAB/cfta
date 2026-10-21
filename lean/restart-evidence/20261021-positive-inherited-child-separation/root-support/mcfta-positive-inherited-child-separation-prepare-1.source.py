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
assert {'geometry', 'independent-review', 'consumer-plan'} == paths
config = [
    ('geometry', 'positive-inherited-child-separation', 'SourceCurrentPositiveInheritedChildSeparation',
     '5810951617d6a97a438c1f3f2393ece29cbffd76884ff836148527cfc62ac8c6'),
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
for pattern in ['mcfta-owner-prefix-decomposition-publication.json', 'mcfta-owner-prefix-decomposition-final-publication*',
                'mcfta-owner-prefix-decomposition-final-push.log', 'mcfta-owner-prefix-decomposition-final-remote.txt',
                'mcfta-owner-prefix-decomposition-board-readback.json', 'mcfta-owner-prefix-decomposition-seal-1.*',
                'mcfta-owner-prefix-decomposition-support-1.*']:
    found = [path for path in Path('/tmp').glob(pattern) if path.is_file()]
    assert found, pattern
    for source in found:
        shutil.copyfile(source, previous / source.name)
print(json.dumps({'status': 'PASS', 'components': len(components), 'new_modules': len(config)}))
