import hashlib
import json
import runpy
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]


def write(name, value):
    (HERE / name).write_text(json.dumps(value, indent=2) + '\n')


selection = {
    'module': 'SourceCurrentFilteredUnionCoverage',
    'strict': 'union-coverage-direct-5',
    'canonical': 'union-coverage-canonical-3',
    'constructed_strict': 'union-coverage-kernels-2',
    'groups': [
        {'name': 'union-coverage-public-1', 'pairs': 2, 'kind': 'new-public', 'full_proof': True},
        {'name': 'union-coverage-kernels-public-1', 'pairs': 1, 'kind': 'constructed', 'full_proof': True},
    ],
}
checker = runpy.run_path(str(HERE / 'verify-probes.py'))
for group in selection['groups']:
    checker['check_group'](group)
for name, expected in [
    ('union-coverage-direct-5', '1bb154e21f58b71cf7b1fb72a53571f125f3fde1494c001020c0111e9051b390'),
    ('union-coverage-kernels-2', 'b5e48ada0ce5ea9970bacf847f270a55b11f0eea1daf7ace0056324965182cb6'),
]:
    receipt = json.loads((HERE / (name + '.json')).read_text())
    assert receipt['exit_code'] == 0 and not (HERE / receipt['log']).read_bytes()
    assert checker['sha'](HERE / receipt['source']) == expected
    checker['check_limits'](name)
write('union-coverage-selection.json', selection)
(HERE / 'union-coverage-report.md').write_text('''# Exact filtered-union coverage

The public parts theorem derives exact literal atoms and full ordinary
rows of actual parent reconstruction. Each part comes from an actual
retained original source member. Mu remains a complete literal atom.
The empty_iff theorem derives the exact physical Empty criterion for all
retained member outputs. Both use actual normalized-parent construction,
warm parent filtering and execution, and warm member calls. Actual finite
preparation supplies those member calls. A warm parent alone does not.

A bare self member is retained only when the entire normalized parent is
that bare self. The proof derives this condition from exact source parts.
The parent-bare case uses both atom uniqueness and absence of ordinary
rows. Member-to-parent inclusion supplies the converse direction.
Physical Empty follows from absence of normal available root parts.

The source-built integration uses an actual used Mu as the own-reference
replacement and Empty at another reference. Preparation derives the full
member schedule and actual parent calls. The filtered parent is Empty,
while the excluded bare self member reconstructs to that nonempty Mu.
The integration invokes both public heads. It assumes no parent result law.

Selected production strict attempt 5 has a zero-byte log. Attempt 1 proves
the initial parts theorem. Attempt 2 retains helper elaboration errors.
Attempts 3 and 4 retain unused-instance and omit warnings. Canonical
attempt 3 is warning-free and matches the final source. Earlier canonical
attempts remain unselected. Fixture strict attempt 2 has a zero-byte log;
attempt 1 retains a constructor-disjointness proof error. Full public2 and
constructed1 probes pass all eight printer settings and standard axioms.

General two-sided source/filter/stored fusion and changing-capture binder
simulation remain open. No Haskell file changes or executable defect.
''')
dependencies = [
    'SourceCurrentFilteredUnionCoverage', 'SourceCurrentGeneratedUnionPreparation',
    'SourceCurrentGeneratedUnionCases', 'SourceCurrentLiteralPartsObservations',
    'SourceCurrentLiteralFilterParts', 'SourceCurrentStoredLiteralExecutionParts',
    'SourceCurrentLiteralUnionParts', 'SourceCurrentLiteralRootParts', 'InternedEmptyNormalization',
]
paths = [ROOT / 'lean/MicroCFTA' / (name + '.lean') for name in dependencies]
paths += [path for path in HERE.glob('union-coverage-*')
          if path.is_file() and not path.name.startswith('union-coverage-review')
          and path.name != 'union-coverage-manifest.json']
paths += [HERE / name for name in ['root-run-check.py', 'root-capped-worker.py', 'verify-probes.py']]
write('union-coverage-manifest.json', {
    'entries': [{'path': str(path.relative_to(ROOT)), 'sha256': hashlib.sha256(path.read_bytes()).hexdigest()}
                for path in sorted(set(paths))],
})
print('Frozen union coverage:', len(set(paths)), 'pins')
