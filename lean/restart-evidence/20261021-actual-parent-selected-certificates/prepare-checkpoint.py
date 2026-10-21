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
assert {'selected', 'independent-review', 'producer-plan', 'sibling-audit'} == paths
config = [
    ('selected', 'selected-certificates', 'SourceCurrentActualParentSelectedCertificates',
     '0f42191fdba120681d238bc40fcde22176ff3c2ab1bebd9ff7d179f971eca732'),
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
for pattern in ['mcfta-actual-owner-pair-publication.json', 'mcfta-actual-owner-pair-final-publication*',
                'mcfta-actual-owner-pair-final-push.log', 'mcfta-actual-owner-pair-final-remote.txt',
                'mcfta-actual-owner-pair-board-readback.json', 'mcfta-actual-owner-pair-seal-1.*',
                'mcfta-actual-owner-pair-support-1.*']:
    found = [path for path in Path('/tmp').glob(pattern) if path.is_file()]
    assert found, pattern
    for source in found:
        shutil.copyfile(source, previous / source.name)
print(json.dumps({'status': 'PASS', 'components': len(components), 'new_modules': len(config)}))
