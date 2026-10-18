import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]


def read(name):
    return json.loads((HERE / name).read_text())


def write(name, value):
    (HERE / name).write_text(json.dumps(value, indent=2) + '\n')


prefixes = ['directed-closure', 'common-reader', 'retained-directed', 'changing-capture']
selections = [read(prefix + '-selection.json') for prefix in prefixes]
names = read('new-modules.json')
groups = [{**group, 'kind': 'new-public' if group['kind'] == 'public' else group['kind']}
          for selected in selections for group in selected['groups']]
assert len(groups) == 7
assert sum(group['pairs'] for group in groups if group['kind'] == 'new-public') == 18
assert sum(group['pairs'] for group in groups if group['kind'] == 'constructed') == 3
assert len(names) == len(selections) == 4
components = [prefix + '-manifest.json' for prefix in prefixes]
components += ['common-reader-review-manifest.json', 'changing-capture-review-manifest.json']
for name in components:
    assert (HERE / name).is_file(), name
stricts = {name: selected['strict'] for name, selected in zip(names, selections)}
canonical = {name: selected['canonical'] for name, selected in zip(names, selections)}
constructed = {}
for selected in selections:
    stems = selected.get('constructed_strict', [])
    stems = [stems] if isinstance(stems, str) else stems
    constructed.update({stem: stem + '.source.lean' for stem in stems})
assert len(constructed) == 3
for name, expected in read('frozen-modules.json').items():
    assert hashlib.sha256((ROOT / 'lean/MicroCFTA' / (name + '.lean')).read_bytes()).hexdigest() == expected
write('selected-groups.json', groups)
write('selected-strict.json', stricts)
write('selected-canonical.json', canonical)
write('selected-constructed-strict.json', constructed)
write('component-manifests.json', components)
write('expected-counts.json', {
    'pairs': {'new-public': 18, 'constructed': 3, 'private-claim': 0},
    'modules': 4, 'constructed_strict': 3, 'components': 6,
})
write('selection-status.json', {'finalized': True})
print(json.dumps({'groups': len(groups), 'public': 18, 'constructed': 3, 'components': 6}))
