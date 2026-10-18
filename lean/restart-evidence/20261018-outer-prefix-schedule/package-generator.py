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
groups = read('outer-fuel-selection.json')['selected_groups'] + read('outer-prefix-selection.json')['groups'] + [
    {'name': 'outer-busy-public-2', 'pairs': 1, 'kind': 'new-public', 'full_proof': True},
    {'name': 'prefix-kernels-public-1', 'pairs': 2, 'kind': 'constructed', 'full_proof': True},
    {'name': 'prefix-claims-public-1', 'pairs': 2, 'kind': 'private-claim', 'full_proof': True},
]
write('selected-groups.json', groups)
write('selected-strict.json', dict(zip(names, [
    'outer-fuel-direct-3', 'outer-prefix-direct-6', 'outer-busy-direct-3'])))
write('selected-canonical.json', dict(zip(names, [
    'outer-fuel-canonical-1', 'outer-prefix-canonical-1', 'outer-busy-canonical-3'])))
write('selected-constructed-strict.json', ['outer-fuel-kernels-1', 'prefix-kernels-7'])
write('selected-audit.json', {'name': 'full-audit-2', 'jobs': 3259, 'dependency_checks': 71290})
write('selection-status.json', {'finalized': True, 'status': 'FINAL'})
write('raw-log-archives.json', [])
write('upstream-refresh.json', {
    'command': ['git', 'pull', '--ff-only'], 'exit_code': 0,
    'output': 'From github.com:TharkunAB/cfta\n   d65cbdb9..67fa7be4  improve/specftacular-correctness-memory -> origin/improve/specftacular-correctness-memory\nAlready up to date.\n',
    'recorded_from_completed_call': True,
    'starting_head': (HERE / 'starting-head.txt').read_text().strip(),
    'main': subprocess.check_output(['git', 'rev-parse', 'origin/main'], cwd=ROOT, text=True).strip(),
    'formalize': subprocess.check_output(['git', 'rev-parse', 'origin/formalize'], cwd=ROOT, text=True).strip(),
    'publication': 'Pending direct approval. No push attempted.'})
write('component-manifests.json', ['outer-fuel-manifest.json', 'outer-prefix-manifest.json',
    'prefix-cross-full-manifest.json', 'root-scope-manifest.json'])
paths = [HERE / name for name in [
    'root-scope-review.md', 'root-peaks.txt', 'root-run-check.py', 'root-capped-worker.py',
    'verify-probes.py', 'verify-checkpoint.py', 'verify-preservation.py', 'verify-closure.py',
    'package-generator.py', 'current-notes-generator.py', 'current-body.txt', 'proof-commit.txt',
    'outer-prefix-kernels.lean', 'root-prefix-kernels.lean']]
for path in HERE.iterdir():
    if path.is_file() and path.name.startswith(('outer-busy-', 'prefix-kernels-', 'prefix-claims-', 'full-audit-')):
        paths.append(path)
for name in names + [
    'SourceCurrentOuterInitialSchedule', 'SourceCurrentOuterInitialActual',
    'SourceCurrentOuterPrefixInvariants', 'SourceCurrentOuterExecutionAncestry',
    'SourceCurrentOuterExecutionGrowth', 'SourceCurrentOuterActiveAncestry',
    'SourceCurrentOuterBusyOwners', 'SourceCurrentOuterEdgeGuardAlphabet',
    'SourceCurrentAllocatedPartialInvariant', 'SourceCurrentAllocatedPartialMemoSound',
    'SourceCurrentAllocatedPartialCallSteps', 'SourceCurrentAllocatedPartialWorker',
    'SourceCurrentInheritedNumeric', 'SourceCurrentParentUniformEnvelope']:
    paths.append(ROOT / 'lean/MicroCFTA' / (name + '.lean'))
write('root-scope-manifest.json', {'component': 'root-scope-review', 'entries': [
    {'path': str(path.relative_to(ROOT)), 'bytes': path.stat().st_size, 'sha256': sha(path)}
    for path in sorted(set(paths))]})
print(json.dumps({'root_scope_entries': len(set(paths)),
    'public_pairs': sum(group['pairs'] for group in groups if group['kind'] == 'new-public'),
    'constructed_pairs': sum(group['pairs'] for group in groups if group['kind'] == 'constructed'),
    'private_claim_pairs': sum(group['pairs'] for group in groups if group['kind'] == 'private-claim')}))
