import hashlib
import json
import subprocess
from pathlib import Path

ROOT = Path('/home/tritlo/Code/mcfta')
HERE = Path(__file__).resolve().parent


def write(name, value):
    (HERE / name).write_text(json.dumps(value, indent=2) + '\n')


def read(name):
    return json.loads((HERE / name).read_text())


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


proof = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip()
(HERE / 'proof-commit.txt').write_text(proof + '\n')
names = ['SourceCurrentGuardHeapBounds', 'SourceCurrentNativeGuardEnvelope', 'SourceCurrentParentAlphabetReservation']
write('new-modules.json', names)
write('frozen-modules.json', {name: sha(ROOT / 'lean/MicroCFTA' / (name + '.lean')) for name in names})
write('selection-status.json', {'finalized': True, 'status': 'FINAL'})
write('raw-log-archives.json', [])
groups = [{'name': 'guard-heap-public-1', 'pairs': 4, 'kind': 'new-public', 'full_proof': True}]
native = read('native-envelope-selection.json')
parent = read('parent-alphabet-selection.json')
kernel = read('native-envelope-kernels-selection.json')
for selected in [native, parent, kernel]:
    groups.extend(selected['selected_groups'])
write('selected-groups.json', groups)
write('selected-strict.json', dict(zip(names, ['guard-heap-direct-2', native['strict'], parent['strict']])))
write('selected-canonical.json', dict(zip(names, ['guard-heap-canonical-1', native['canonical'], parent['canonical']])))
write('selected-constructed-strict.json', [parent['constructed_strict'], 'native-envelope-kernels-' + str(kernel['selected_attempt'])])
write('selected-audit.json', {'name': 'full-audit-1', 'jobs': 3237, 'dependency_checks': 70923})
write('upstream-refresh.json', {
    'command': ['git', 'pull', '--ff-only'], 'exit_code': 0,
    'stdout': 'Already up to date.\n', 'recorded_from_completed_call': True,
    'starting_head': (HERE / 'starting-head.txt').read_text().strip(),
    'main': 'c0cc8a0582cd6b01c344ec15f949ecb46a72dc0e',
    'formalize': 'a1270b81422ea48ffe0a84f2c774e6c7c1f86b0a',
    'publication': 'Pending direct approval. No push attempted.',
})
write('component-manifests.json', [
    'native-envelope-manifest.json', 'parent-alphabet-manifest.json',
    'native-envelope-kernels-manifest.json', 'review-envelope-manifest.json',
    'guard-envelope-review-manifest.json', 'root-scope-manifest.json',
])
paths = [HERE / name for name in [
    'root-scope-review.md', 'root-peaks.txt', 'root-run-check.py', 'root-capped-worker.py',
    'verify-probes.py', 'verify-checkpoint.py', 'package-generator.py', 'current-notes-generator.py',
]]
for path in HERE.iterdir():
    if path.is_file() and path.name.startswith(('guard-heap-', 'full-audit-')):
        paths.append(path)
for name in names + [
    'SourceCurrentAllocatedFiniteOrdinaryGuardLimits', 'SourceCurrentAllocatedFiniteOrdinaryGuardOwn',
    'SourceCurrentGeneratedQueryGuardResources', 'SourceCurrentNativeGuardAlphabet',
    'SourceCurrentConjunctionGuardUniverse', 'SourceCurrentParentNumeric', 'SourceCurrentClassesForecast',
]:
    paths.append(ROOT / 'lean/MicroCFTA' / (name + '.lean'))
write('root-scope-manifest.json', {
    'component': 'root-scope-review',
    'entries': [{'path': str(path.relative_to(ROOT)), 'bytes': path.stat().st_size, 'sha256': sha(path)}
                for path in sorted(set(paths))],
})
print(json.dumps({'proof_commit': proof, 'root_scope_entries': len(set(paths))}))
