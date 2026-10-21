import hashlib
import json
import shutil
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
def write(name, value):
    (HERE / name).write_text(json.dumps(value, indent=2) + '\n')
components = json.loads((HERE / 'components.json').read_text())
assert {item['path'] for item in components} == {'stores', 'independent-review', 'scan-plan'}
selection = json.loads((HERE / 'stores/query-stores-selection.json').read_text())
assert selection['new_public_pairs'] == 2 and selection['lean_jobs'] == 5
config = [
    ('request', 'SourceCurrentNativeRequestPositivePositions',
     'e9fe573b314f7e8e4bf65025bb29078165a61a5fa92168f3da65b852b47d4d52', 'query-stores-public-1'),
    ('current', 'SourceCurrentNativeCurrentStores',
     '48b80476a09c7b4c3f5ce1ef1b35b45cadc6acc6d6f7a401637cadb4f010a728', 'current-stores-public-1'),
]
sources, frozen, checks = {}, {}, {}
for tag, module, expected, public in config:
    name = 'lean/MicroCFTA/' + module + '.lean'
    digest = hashlib.sha256((ROOT / name).read_bytes()).hexdigest()
    assert digest == expected
    sources[name] = {'sha256': digest}
    frozen[module] = digest
    checks[tag] = {'strict': tag + '-strict-1', 'public': 'stores/' + public}
write('selected-sources.json', sources)
write('frozen-modules.json', frozen)
write('selected-checks.json', {**checks, 'audit': 'audit-1'})
previous = HERE / 'previous-publication-support'
previous.mkdir()
for pattern in ['mcfta-positive-owner-pair-publication.json', 'mcfta-positive-owner-pair-final-publication*',
                'mcfta-positive-owner-pair-final-push.log', 'mcfta-positive-owner-pair-final-remote.txt',
                'mcfta-positive-owner-pair-board-readback.json', 'mcfta-positive-owner-pair-seal-1.*',
                'mcfta-positive-owner-pair-support-1.*']:
    found = [path for path in Path('/tmp').glob(pattern) if path.is_file()]
    assert found, pattern
    for source in found:
        shutil.copyfile(source, previous / source.name)
print(json.dumps({'status': 'PASS', 'components': len(components), 'new_modules': 1,
                  'additive_module_updates': 1, 'public_heads': 2}))
