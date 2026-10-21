import hashlib
import json
import shutil
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]

def write(name, value):
    (HERE / name).write_text(json.dumps(value, indent=2) + '\n')

components = json.loads((HERE / 'components.json').read_text())
assert {item['path'] for item in components} == {
    'capacity-plan', 'semantic-next-plan', 'semantic-plan-review',
    'cold-capacity', 'capacity-independent-review', 'cold-semantic', 'semantic-independent-review'}
config = [
    ('cold-capacity', 'cold-rank-capacity', 'SourceCurrentColdRankCapacity', 'producer-strict-1'),
    ('cold-semantic', 'cold-rank-semantic', 'SourceCurrentColdRankSemantic', 'semantic-strict-1'),
]
sources, frozen, checks = {}, {}, {}
for tag, prefix, module, strict in config:
    selection = json.loads((HERE / tag / (prefix + '-selection.json')).read_text())
    assert selection['finalized']
    name = 'lean/MicroCFTA/' + module + '.lean'
    digest = hashlib.sha256((ROOT / name).read_bytes()).hexdigest()
    assert digest == selection['source_sha256']
    sources[name] = {'sha256': digest}
    frozen[module] = digest
    checks[tag] = {'strict': strict, 'public': tag + '/' + selection['selected_public']}
write('selected-sources.json', sources)
write('frozen-modules.json', frozen)
write('selected-checks.json', {**checks, 'audit': 'audit-2'})
previous = HERE / 'previous-publication-support'
previous.mkdir()
for pattern in ['mcfta-outer-rank-adequacy-publication.json', 'mcfta-outer-rank-adequacy-final-publication*',
                'mcfta-outer-rank-adequacy-final-push.log', 'mcfta-outer-rank-adequacy-final-remote.txt',
                'mcfta-outer-rank-adequacy-board-readback.json', 'mcfta-outer-rank-adequacy-seal-1.*',
                'mcfta-outer-rank-adequacy-support-1.*']:
    found = [path for path in Path('/tmp').glob(pattern) if path.is_file()]
    assert found, pattern
    for source in found:
        shutil.copyfile(source, previous / source.name)
print(json.dumps({'status': 'PASS', 'components': len(components), 'new_modules': len(config)}))
