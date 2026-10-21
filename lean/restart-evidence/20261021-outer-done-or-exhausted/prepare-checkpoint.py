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
assert {'done-or-exhausted', 'independent-review', 'adequacy-plan', 'adequacy-plan-review'} == paths
config = [
    ('done-or-exhausted', 'outer-done-or-exhausted', 'SourceCurrentOuterDoneOrExhausted',
     'b6485bba37a65fd0358d00517605198c7ad74d53d1341d13ab0c6093f10cc3ce'),
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
for pattern in ['mcfta-outer-local-faults-publication.json', 'mcfta-outer-local-faults-final-publication*',
                'mcfta-outer-local-faults-final-push.log', 'mcfta-outer-local-faults-final-remote.txt',
                'mcfta-outer-local-faults-board-readback.json', 'mcfta-outer-local-faults-seal-1.*',
                'mcfta-outer-local-faults-support-1.*']:
    found = [path for path in Path('/tmp').glob(pattern) if path.is_file()]
    assert found, pattern
    for source in found:
        shutil.copyfile(source, previous / source.name)
print(json.dumps({'status': 'PASS', 'components': len(components), 'new_modules': len(config)}))
