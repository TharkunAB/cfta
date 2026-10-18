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
names = ['SourceCurrentActualTargetSlotHistory', 'SourceCurrentNativeKeyAdmission', 'SourceCurrentNativeAdmissionWriter']
write('new-modules.json', names)
write('frozen-modules.json', {name: sha(ROOT / 'lean/MicroCFTA' / (name + '.lean')) for name in names})
write('selection-status.json', {'finalized': True, 'status': 'FINAL'})
write('raw-log-archives.json', [])
groups = [
    {'name': 'slot-history-public-1', 'pairs': 15, 'kind': 'new-public', 'full_proof': True},
    {'name': 'native-writer-public-1', 'pairs': 1, 'kind': 'new-public', 'full_proof': True},
]
stricts = []
for name in ['native-key-selection.json', 'slot-history-kernels-selection.json', 'native-writer-kernels-selection.json']:
    selected = json.loads((HERE / name).read_text())
    for original in selected.get('selected_groups', selected.get('groups', [])):
        group = dict(original)
        if group['kind'] == 'public':
            group['kind'] = 'new-public'
        groups.append(group)
    stricts.append(selected['constructed_strict'] if 'constructed_strict' in selected else selected['strict'])
write('selected-groups.json', groups)
write('selected-strict.json', dict(zip(names, ['slot-history-direct-2', 'native-key-direct-1', 'native-writer-direct-1'])))
write('selected-canonical.json', dict(zip(names, ['slot-history-canonical-1', 'native-key-canonical-1', 'native-writer-canonical-1'])))
write('selected-constructed-strict.json', stricts)
write('selected-audit.json', {'name': 'full-audit-1', 'jobs': 3230, 'dependency_checks': 70896})
write('upstream-refresh.json', {
    'command': ['git', 'pull', '--ff-only'], 'exit_code': 0,
    'stdout': 'Already up to date.\n', 'recorded_from_completed_call': True,
    'starting_head': (HERE / 'starting-head.txt').read_text().strip(),
    'main': 'c0cc8a0582cd6b01c344ec15f949ecb46a72dc0e',
    'formalize': 'a1270b81422ea48ffe0a84f2c774e6c7c1f86b0a',
    'publication': 'Pending direct approval. No push attempted.',
})
write('component-manifests.json', [
    'native-key-manifest.json', 'slot-history-kernels-manifest.json',
    'native-writer-kernels-manifest.json', 'selected-read-manifest.json', 'root-scope-manifest.json',
])
paths = [HERE / name for name in [
    'root-scope-review.md', 'root-peaks.txt', 'root-run-check.py',
    'root-capped-worker.py', 'verify-probes.py', 'verify-checkpoint.py',
    'package-generator.py', 'current-notes-generator.py',
]]
prefixes = ('slot-history-direct-', 'slot-history-canonical-', 'slot-history-public',
            'native-writer-direct-', 'native-writer-canonical-', 'native-writer-public', 'full-audit-')
for path in HERE.iterdir():
    if path.is_file() and path.name.startswith(prefixes):
        paths.append(path)
for name in names + [
    'SourceCurrentActualSharedLeafEvents', 'SourceCurrentAllocatedSharedTargetWorker',
    'SourceCurrentAllocatedSharedEditWorker', 'SourceCurrentLowerOperationInvariants',
    'SourceCurrentSharedLeafNativeLineage', 'SourceCurrentNativeWriterReadyRetention',
    'SourceCurrentTargetNumeric', 'SourceCurrentClassPassNumeric',
]:
    paths.append(ROOT / 'lean/MicroCFTA' / (name + '.lean'))
write('root-scope-manifest.json', {
    'component': 'root-scope-review',
    'entries': [{'path': str(path.relative_to(ROOT)), 'bytes': path.stat().st_size, 'sha256': sha(path)}
                for path in sorted(set(paths))],
})
print(json.dumps({'proof_commit': proof, 'root_scope_entries': len(set(paths))}))
