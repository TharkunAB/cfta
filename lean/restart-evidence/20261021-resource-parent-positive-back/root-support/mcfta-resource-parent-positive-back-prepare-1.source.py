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
assert {'back', 'independent-review', 'rank-plan'} == paths
config = [
    ('back', 'resource-parent-positive-back', 'SourceCurrentResourceParentPositiveBack',
     'fa63f2d89d8494b24e5563bff710f4d9eab9b887a951ee16a1ab28660c04fc7e'),
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
for pattern in ['mcfta-positive-quotient-count-publication.json', 'mcfta-positive-quotient-count-final-publication*',
                'mcfta-positive-quotient-count-final-push.log', 'mcfta-positive-quotient-count-final-remote.txt',
                'mcfta-positive-quotient-count-board-readback.json', 'mcfta-positive-quotient-count-seal-1.*',
                'mcfta-positive-quotient-count-support-1.*']:
    found = [path for path in Path('/tmp').glob(pattern) if path.is_file()]
    assert found, pattern
    for source in found:
        shutil.copyfile(source, previous / source.name)
print(json.dumps({'status': 'PASS', 'components': len(components), 'new_modules': len(config)}))
