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
assert {'closed', 'independent-review', 'outer-closure-plan', 'completion-audit-review', 'outer-closure-plan-review'} == paths
config = [
    ('closed', 'resource-parent-closed', 'SourceCurrentResourceParentClosed',
     'dfa0774e42398c9dcd43b1e846e71cc96092f431fea30985bbe39d8fd3dd9946'),
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
for pattern in ['mcfta-older-owner-busy-publication.json', 'mcfta-older-owner-busy-final-publication*',
                'mcfta-older-owner-busy-final-push.log', 'mcfta-older-owner-busy-final-remote.txt',
                'mcfta-older-owner-busy-board-readback.json', 'mcfta-older-owner-busy-seal-1.*',
                'mcfta-older-owner-busy-support-1.*']:
    found = [path for path in Path('/tmp').glob(pattern) if path.is_file()]
    assert found, pattern
    for source in found:
        shutil.copyfile(source, previous / source.name)
print(json.dumps({'status': 'PASS', 'components': len(components), 'new_modules': len(config)}))
