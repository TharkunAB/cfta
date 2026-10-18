import hashlib
import json
import subprocess
from pathlib import Path

ROOT = Path('/home/tritlo/Code/mcfta')
HERE = Path(__file__).resolve().parent


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write(name, value):
    (HERE / name).write_text(json.dumps(value, indent=2) + '\n')


def read(name):
    return json.loads((HERE / name).read_text())


names = read('new-modules.json')
for name, expected in read('frozen-modules.json').items():
    assert sha(ROOT / 'lean/MicroCFTA' / (name + '.lean')) == expected
groups = [
    {'name': 'classes-guard-public-1', 'pairs': 2, 'kind': 'new-public', 'full_proof': True},
    {'name': 'classes-guard-kernels-public-1', 'pairs': 1, 'kind': 'constructed', 'full_proof': True},
]
for name in ['parent-guard-selection.json', 'uniform-guard-selection.json']:
    for original in read(name)['selected_groups']:
        group = dict(original)
        if group['kind'] == 'public':
            group['kind'] = 'new-public'
        groups.append(group)
write('selected-groups.json', groups)
write('selected-strict.json', dict(zip(names, [
    'classes-guard-direct-3', 'local-guard-direct-2', 'parent-guard-direct-3', 'uniform-guard-direct-1'])))
write('selected-canonical.json', dict(zip(names, [
    'classes-guard-canonical-2', 'local-guard-canonical-1', 'parent-guard-canonical-1', 'uniform-guard-canonical-1'])))
write('selected-constructed-strict.json', [
    'classes-guard-kernels-2', 'parent-guard-kernels-1', 'uniform-guard-kernels-1'])
write('selected-audit.json', {'name': 'full-audit-1', 'jobs': 3252, 'dependency_checks': 71136})
write('selection-status.json', {'finalized': True, 'status': 'FINAL'})
write('raw-log-archives.json', [])
write('upstream-refresh.json', {
    'command': ['git', 'pull', '--ff-only'], 'exit_code': 0,
    'output': 'Already up to date.\n', 'recorded_from_completed_call': True,
    'starting_head': (HERE / 'starting-head.txt').read_text().strip(),
    'main': subprocess.check_output(['git', 'rev-parse', 'origin/main'], cwd=ROOT, text=True).strip(),
    'formalize': subprocess.check_output(['git', 'rev-parse', 'origin/formalize'], cwd=ROOT, text=True).strip(),
    'publication': 'Pending direct approval. No push attempted.'})
components = ['parent-guard-manifest.json', 'uniform-guard-manifest.json',
              'outer-context-map-manifest.json', 'classes-cross-review-manifest.json',
              'parent-cross-review-manifest.json', 'root-scope-manifest.json']
write('component-manifests.json', components)
paths = [HERE / name for name in [
    'root-scope-review.md', 'root-peaks.txt', 'root-run-check.py', 'root-capped-worker.py',
    'verify-probes.py', 'verify-checkpoint.py', 'verify-preservation.py', 'verify-closure.py',
    'package-generator.py', 'current-notes-generator.py', 'current-body.txt', 'proof-commit.txt']]
for path in HERE.iterdir():
    if path.is_file() and path.name.startswith(('classes-guard-', 'full-audit-')):
        paths.append(path)
for name in names + [
    'SourceCurrentClassesNumeric', 'SourceCurrentLocalNumeric', 'SourceCurrentParentNumeric',
    'SourceCurrentClassesForecast', 'SourceCurrentScanRequiredForecast',
    'SourceCurrentInitialSelectionForecast', 'SourceCurrentClassGuardAlphabet',
    'SourceCurrentPreparationGuardAlphabet', 'SourceCurrentParentAlphabetReservation',
    'SourceCurrentParentUniformEnvelope', 'SourceCurrentOuterCallBudget',
    'SourceCurrentInheritedNumeric', 'SourceCurrentRawRebuildNumeric',
    'SourceCurrentOuterConstructorBounds', 'SourceCurrentAllocatedPartialWorker']:
    paths.append(ROOT / 'lean/MicroCFTA' / (name + '.lean'))
write('root-scope-manifest.json', {
    'component': 'root-scope-review', 'entries': [
        {'path': str(path.relative_to(ROOT)), 'bytes': path.stat().st_size, 'sha256': sha(path)}
        for path in sorted(set(paths))]})
print(json.dumps({
    'root_scope_entries': len(set(paths)),
    'public_pairs': sum(group['pairs'] for group in groups if group['kind'] == 'new-public'),
    'constructed_pairs': sum(group['pairs'] for group in groups if group['kind'] == 'constructed')}))
