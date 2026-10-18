import json
from pathlib import Path

ROOT = Path('/home/tritlo/Code/mcfta')
HERE = ROOT / 'lean/restart-evidence/20261018-open-binder-source-induction'


def read(name):
    return json.loads((HERE / name).read_text())


def write(name, value):
    (HERE / name).write_text(json.dumps(value, indent=2) + '\n')


boundary = read('open-binder-boundary-selection.json')
selections = [read(name) for name in ['publication-body-source-selection.json',
              'open-binder-simulation-selection.json', 'retained-mu-language-selection.json',
              'preorder-normalization-review-selection.json', 'open-binder-boundary-selection.json']]
groups = [group for selection in selections for group in selection['groups']]
groups = [{**group, 'kind': 'new-public' if group['kind'] == 'public' else group['kind']} for group in groups]
assert sum(g['pairs'] for g in groups if g['kind'] == 'new-public') == 16
assert sum(g['pairs'] for g in groups if g['kind'] == 'constructed') == 3
stricts = {'SourceCurrentPublicationBodySourceCases': 'publication-body-source-direct-5',
           'SourceCurrentRetainedMuFiniteUnfoldEquation': 'retained-mu-equation-direct-2',
           'SourceCurrentOpenPreorderSimulation': 'open-binder-simulation-direct-1',
           'SourceCurrentOpenObservationLanguage': 'open-observation-language-direct-2',
           'SourceCurrentOpenBinderObservationBoundary': boundary['strict']}
canonical = {'SourceCurrentPublicationBodySourceCases': 'publication-body-source-canonical-1',
             'SourceCurrentRetainedMuFiniteUnfoldEquation': 'retained-mu-equation-canonical-2',
             'SourceCurrentOpenPreorderSimulation': 'open-binder-simulation-canonical-1',
             'SourceCurrentOpenObservationLanguage': 'open-observation-language-canonical-1',
             'SourceCurrentOpenBinderObservationBoundary': boundary['canonical']}
constructed = {'retained-mu-equation-kernels-2': 'retained-mu-equation-kernels.lean',
               'preorder-normalization-review-kernels-5': 'preorder-normalization-review-kernels-5.source.lean'}
components = ['publication-body-source-manifest.json', 'open-binder-simulation-manifest.json',
              'preorder-normalization-review-manifest.json', 'open-language-review-manifest.json',
              'open-binder-boundary-manifest.json', 'open-binder-boundary-review-manifest.json']
for name in components:
    assert (HERE / name).is_file(), name
write('selected-groups.json', groups)
write('selected-strict.json', stricts)
write('selected-canonical.json', canonical)
write('selected-constructed-strict.json', constructed)
write('component-manifests.json', components)
write('expected-counts.json', {'pairs': {'new-public': 16, 'constructed': 3, 'private-claim': 0},
                              'modules': 5, 'constructed_strict': 2, 'components': 6})
write('selection-status.json', {'finalized': True})
print(json.dumps({'groups': len(groups), 'public': 16, 'constructed': 3, 'components': 6}))
