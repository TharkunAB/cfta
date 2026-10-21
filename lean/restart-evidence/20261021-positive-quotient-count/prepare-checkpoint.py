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
assert {'count', 'independent-review', 'back-plan'} == paths
config = [
    ('count', 'positive-quotient-count', 'SourceCurrentPositiveQuotientCount',
     '7647bb4b3f89be344e4e97711a81c8cf2d9326edffa867692c1b10f7478b14ca'),
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
for pattern in ['mcfta-resource-owner-inherited-dispatch-publication.json', 'mcfta-resource-owner-inherited-dispatch-final-publication*',
                'mcfta-resource-owner-inherited-dispatch-final-push.log', 'mcfta-resource-owner-inherited-dispatch-final-remote.txt',
                'mcfta-resource-owner-inherited-dispatch-board-readback.json', 'mcfta-resource-owner-inherited-dispatch-seal-1.*',
                'mcfta-resource-owner-inherited-dispatch-support-1.*']:
    found = [path for path in Path('/tmp').glob(pattern) if path.is_file()]
    assert found, pattern
    for source in found:
        shutil.copyfile(source, previous / source.name)
print(json.dumps({'status': 'PASS', 'components': len(components), 'new_modules': len(config)}))
