import hashlib
import json
import subprocess
from pathlib import Path

ROOT = Path('/home/tritlo/Code/mcfta')
HERE = Path(__file__).resolve().parent


def write(name, value):
    (HERE / name).write_text(json.dumps(value, indent=2) + '\n')


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


proof = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip()
(HERE / 'proof-commit.txt').write_text(proof + '\n')
names = ['SourceCurrentActualParentRowOrigins', 'SourceCurrentPositionalOriginChain']
write('new-modules.json', names)
write('frozen-modules.json', {name: sha(ROOT / 'lean/MicroCFTA' / (name + '.lean')) for name in names})
write('selection-status.json', {'finalized': True, 'status': 'FINAL'})
write('raw-log-archives.json', [])
groups = [
    {'name': 'parent-origin-public-2', 'pairs': 3, 'kind': 'new-public', 'full_proof': True},
    {'name': 'chain-public-1', 'pairs': 5, 'kind': 'new-public', 'full_proof': True},
    {'name': 'chain-kernels-public-1', 'pairs': 1, 'kind': 'constructed', 'full_proof': True},
]
stricts = ['chain-kernels-2']
for name in ['parent-selected-selection.json', 'schedule-review-selection.json']:
    selected = json.loads((HERE / name).read_text())
    groups.extend(selected['groups'])
    stricts.append(selected['strict'])
write('selected-groups.json', groups)
write('selected-strict.json', dict(zip(names, ['parent-origin-direct-3', 'chain-direct-2'])))
write('selected-canonical.json', dict(zip(names, ['parent-origin-canonical-3', 'chain-canonical-1'])))
write('selected-constructed-strict.json', stricts)
write('selected-audit.json', {'name': 'full-audit-1', 'jobs': 3223, 'dependency_checks': 70834})
write('upstream-refresh.json', {
    'command': ['git', 'pull', '--ff-only'], 'exit_code': 0,
    'stdout': 'Already up to date.\n', 'recorded_from_completed_call': True,
    'starting_head': (HERE / 'starting-head.txt').read_text().strip(),
    'main': 'c0cc8a0582cd6b01c344ec15f949ecb46a72dc0e',
    'formalize': 'a1270b81422ea48ffe0a84f2c774e6c7c1f86b0a',
    'publication': 'Pending direct approval. No push attempted.',
})
write('component-manifests.json', [
    'chain-manifest.json', 'parent-selected-manifest.json',
    'schedule-review-manifest.json', 'root-scope-manifest.json',
])
paths = [HERE / name for name in [
    'root-scope-review.md', 'root-peaks.txt', 'root-run-check.py',
    'root-capped-worker.py', 'verify-probes.py', 'verify-checkpoint.py',
    'package-generator.py', 'current-notes-generator.py',
]]
for path in HERE.iterdir():
    if path.is_file() and path.name.startswith(('parent-origin-', 'full-audit-')):
        paths.append(path)
for name in names + [
    'SourceCurrentActualLocalReduceRowOrigins', 'SourceCurrentAllocatedParentWorker',
    'SourceCurrentAllocatedMkEdge', 'SourceEqualityMkEdgeAllocation',
    'SourceCurrentParentOperationInvariants', 'SourceCurrentActualRequiredRowOrigins',
    'SourceCurrentPositionalOriginDescent', 'SourceCurrentAllocatedPartialWorker',
]:
    paths.append(ROOT / 'lean/MicroCFTA' / (name + '.lean'))
write('root-scope-manifest.json', {
    'component': 'root-scope-review',
    'entries': [{'path': str(path.relative_to(ROOT)), 'bytes': path.stat().st_size, 'sha256': sha(path)}
                for path in sorted(set(paths))],
})
print(json.dumps({'proof_commit': proof, 'root_scope_entries': len(set(paths))}))
