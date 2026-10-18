import hashlib
import json
import runpy
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]


def write(name, value):
    (HERE / name).write_text(json.dumps(value, indent=2) + '\n')


selection = {
    'module': 'SourceCurrentStoredNonemptyReplacement',
    'strict': 'nonempty-replacement-direct-4',
    'canonical': 'nonempty-replacement-canonical-1',
    'constructed_strict': 'nonempty-replacement-kernels-direct-2',
    'groups': [
        {'name': 'nonempty-replacement-public-1', 'pairs': 2, 'kind': 'new-public', 'full_proof': True},
        {'name': 'nonempty-replacement-kernels-public-1', 'pairs': 1, 'kind': 'constructed', 'full_proof': True},
    ],
}
checker = runpy.run_path(str(HERE / 'verify-probes.py'))
for group in selection['groups']:
    checker['check_group'](group)
for name, expected in [
    ('nonempty-replacement-direct-4', 'e04d1fb538ec4533b02244ada1896b8fb13d869a11f50f9f5d6f6e4ddc5cb69b'),
    ('nonempty-replacement-kernels-direct-2', '9e5938c2309178e7bc7899bad1ef2e253e8a4b5fe353df0b0661b22014645a9f'),
]:
    receipt = json.loads((HERE / (name + '.json')).read_text())
    assert receipt['exit_code'] == 0 and not (HERE / receipt['log']).read_bytes()
    assert checker['sha'](HERE / receipt['source']) == expected
    checker['check_limits'](name)
write('nonempty-replacement-selection.json', selection)
(HERE / 'nonempty-replacement-report.md').write_text('''# Nonempty stored replacement

The two public heads are execute_nonempty and unfold_mu. They compare
physical Empty constructor tests. They do not prove language inhabitance.
The first requires nonempty resolved replacements only on original free
names. Actual execution, initial Ready and availability remain explicit.
The second derives the replacement facts for actual unfolding by the Mu.
Its comparison is with the stored body, not with the Mu record itself.

Identity input costs give positive singleton meanings. Exact canonical
slots retain the original closed captures. Occurrence support and full
stored-plan retention prove the identity Empty test. An actual complete
identity call and original-free-name Empty congruence give the result.
The proof includes arbitrary open nested Mu values.

Production direct attempt 4 is the final zero-byte strict log. Attempts
1 and 2 retain elaboration errors. Attempt 3 proves the first head before
the Mu corollary was added. Canonical attempt 1 is warning-free. The full
public probe checks both statements, proofs and standard axiom sets.

The concrete integration derives initial facts from source construction.
It retains distinct available nonempty replacements and two sequential
stored calls. It also constructs an actual used-Mu unfolding. It invokes
both public heads. Strict fixture attempt 2 has a zero-byte log. Attempt
1 retains a constructor-inequality proof error. One full constructed head
passes all eight printer/linter settings and standard-axiom checks.

General Generated Empty fusion, distinct-plan simulation and arbitrary
source-built recursive semantic instances remain open. No Haskell file
changes or executable defects are added.
''')
dependencies = [
    'SourceCurrentStoredNonemptyReplacement', 'SourceCurrentStoredEmptyCongruence',
    'SourceCurrentStoredEmptyInterpreter', 'SourceCurrentStoredReconstruction',
    'InternedStoredCostRetention', 'InternedStoredCostInputs',
    'InternedStoredSubstitutionScope', 'InternedFreeOccurrenceRank',
    'InternedRecordDepthShape', 'InternedDepthSemanticProjections',
]
paths = [ROOT / 'lean/MicroCFTA' / (name + '.lean') for name in dependencies]
paths += [path for path in HERE.glob('nonempty-replacement-*')
          if path.is_file() and not path.name.startswith('nonempty-replacement-review')
          and path.name != 'nonempty-replacement-manifest.json']
paths += [HERE / name for name in ['root-run-check.py', 'root-capped-worker.py', 'verify-probes.py']]
write('nonempty-replacement-manifest.json', {
    'entries': [{'path': str(path.relative_to(ROOT)), 'sha256': hashlib.sha256(path.read_bytes()).hexdigest()}
                for path in sorted(set(paths))],
})
print('Frozen nonempty replacement component:', len(set(paths)), 'pins')
