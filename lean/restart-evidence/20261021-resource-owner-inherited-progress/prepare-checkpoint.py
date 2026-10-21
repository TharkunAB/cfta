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
assert {'progress', 'independent-review', 'dispatch-plan'} == paths
config = [
    ('progress', 'resource-owner-inherited-progress', 'SourceCurrentResourceOwnerInheritedProgress',
     'aae1b162215c806a9890337a4fad9ad20f1b6deca5ce30a14c902a8c36bf4dd3'),
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
for pattern in ['mcfta-positive-inherited-child-separation-publication.json', 'mcfta-positive-inherited-child-separation-final-publication*',
                'mcfta-positive-inherited-child-separation-final-push.log', 'mcfta-positive-inherited-child-separation-final-remote.txt',
                'mcfta-positive-inherited-child-separation-board-readback.json', 'mcfta-positive-inherited-child-separation-seal-1.*',
                'mcfta-positive-inherited-child-separation-support-1.*']:
    found = [path for path in Path('/tmp').glob(pattern) if path.is_file()]
    assert found, pattern
    for source in found:
        shutil.copyfile(source, previous / source.name)
print(json.dumps({'status': 'PASS', 'components': len(components), 'new_modules': len(config)}))
