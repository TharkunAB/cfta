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
assert {'rank', 'independent-review', 'body-plan'} == paths
config = [
    ('rank', 'actual-child-rank', 'SourceCurrentActualChildRank',
     'f4f2e895519d57d582a4422676cc3bca3b1896c95868883698bc2a5e7361f3d4'),
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
for pattern in ['mcfta-resource-parent-positive-back-publication.json', 'mcfta-resource-parent-positive-back-final-publication*',
                'mcfta-resource-parent-positive-back-final-push.log', 'mcfta-resource-parent-positive-back-final-remote.txt',
                'mcfta-resource-parent-positive-back-board-readback.json', 'mcfta-resource-parent-positive-back-seal-1.*',
                'mcfta-resource-parent-positive-back-support-1.*']:
    found = [path for path in Path('/tmp').glob(pattern) if path.is_file()]
    assert found, pattern
    for source in found:
        shutil.copyfile(source, previous / source.name)
print(json.dumps({'status': 'PASS', 'components': len(components), 'new_modules': len(config)}))
