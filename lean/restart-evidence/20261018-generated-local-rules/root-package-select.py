import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]


def read(name):
    return json.loads((HERE / name).read_text())


def write(name, value):
    (HERE / name).write_text(json.dumps(value, indent=2) + '\n')


names = read('new-modules.json')
prefixes = ['lexical', 'generated-node', 'generated-union']
selections = [read(prefix + '-selection.json') for prefix in prefixes]
groups = [{**group, 'kind': 'new-public' if group['kind'] == 'public' else group['kind']}
          for selected in selections for group in selected['groups']]
boundary = read('generated-empty-selection.json')
groups += boundary['groups']
assert sum(group['pairs'] for group in groups if group['kind'] == 'new-public') == 7
assert sum(group['pairs'] for group in groups if group['kind'] == 'constructed') == 3
assert len(names) == len(selections) == 3
components = [prefix + '-manifest.json' for prefix in prefixes]
components += ['generated-empty-manifest.json', 'generated-union-lexical-review-manifest.json']
node_review = HERE / 'generated-empty-node-review-manifest.json'
if node_review.is_file():
    components.append(node_review.name)
for name in components:
    assert (HERE / name).is_file(), name
stricts = {name: selected['strict'] for name, selected in zip(names, selections)}
canonical = {name: selected['canonical'] for name, selected in zip(names, selections)}
constructed = {}
for selected, working in zip(selections[1:] + [boundary],
                             ['generated-node-kernels.lean', 'generated-union-kernels.lean',
                              'generated-empty-boundary.lean']):
    stems = selected.get('constructed_strict', [])
    stems = [stems] if isinstance(stems, str) else stems
    assert len(stems) == 1, selected
    constructed[stems[0]] = working
for name, expected in read('frozen-modules.json').items():
    assert hashlib.sha256((ROOT / 'lean/MicroCFTA' / (name + '.lean')).read_bytes()).hexdigest() == expected
write('selected-groups.json', groups)
write('selected-strict.json', stricts)
write('selected-canonical.json', canonical)
write('selected-constructed-strict.json', constructed)
write('component-manifests.json', components)
write('expected-counts.json', {
    'pairs': {'new-public': 7, 'constructed': 3, 'private-claim': 0},
    'modules': 3, 'constructed_strict': 3, 'components': len(components),
})
write('selection-status.json', {'finalized': True})
log = (HERE / 'full-audit-1.log').read_text()
write('selected-audit.json', {
    'name': 'full-audit-1',
    'jobs': int(re.findall(r'Build completed successfully \((\d+) jobs\)\.', log)[-1]),
    'dependency_checks': int(re.findall(r'Checked axiom dependencies of (\d+) MicroCFTA theorems\.', log)[-1]),
})
print(json.dumps({'groups': len(groups), 'public': 7, 'constructed': 3, 'components': len(components)}))
