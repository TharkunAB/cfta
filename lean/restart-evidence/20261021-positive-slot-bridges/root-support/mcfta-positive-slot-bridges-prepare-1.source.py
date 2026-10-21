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
assert {'advance', 'value', 'advance-review', 'value-review', 'slot-plan'} <= paths
config = [
    ('advance', 'support-advance', 'SourceCurrentNativePositiveSupportAdvance',
     'd0b9482f3a3558eeba112de5ed3216c1be00d425deb1bf0915c2bbda53bee154'),
    ('value', 'raw-value', 'SourceCurrentRawCorridorPositiveValue',
     'b55beb1901b9a41c8c3007cb1f318e5d91dda9297390dc82bbabbb659a016047'),
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
for pattern in ['mcfta-positive-query-raw-projection-publication.json', 'mcfta-positive-query-raw-projection-final-publication*',
                'mcfta-positive-query-raw-projection-final-push.log', 'mcfta-positive-query-raw-projection-final-remote.txt',
                'mcfta-positive-query-raw-projection-board-readback.json', 'mcfta-positive-query-raw-projection-seal-1.*',
                'mcfta-positive-query-raw-projection-support-1.*']:
    found = [path for path in Path('/tmp').glob(pattern) if path.is_file()]
    assert found, pattern
    for source in found:
        shutil.copyfile(source, previous / source.name)
print(json.dumps({'status': 'PASS', 'components': len(components), 'new_modules': len(config)}))
