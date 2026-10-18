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
    {'name': 'outer-schedule-public-1', 'pairs': 17, 'kind': 'new-public', 'full_proof': True},
    {'name': 'outer-actual-kernels-public-2', 'pairs': 1, 'kind': 'constructed', 'full_proof': True},
    {'name': 'outer-actual-claim-public-1', 'pairs': 1, 'kind': 'private-claim', 'full_proof': True},
]
for name, key in [('outer-edge-selection.json', 'selected_groups'),
                  ('outer-rebuild-selection.json', 'selected_groups'),
                  ('outer-actual-selection.json', 'groups')]:
    groups.extend(read(name)[key])
write('selected-groups.json', groups)
write('selected-strict.json', dict(zip(names, [
    'outer-schedule-direct-3', 'outer-edge-direct-1', 'outer-rebuild-direct-1', 'outer-actual-direct-5'])))
write('selected-canonical.json', dict(zip(names, [
    'outer-schedule-canonical-1', 'outer-edge-canonical-1', 'outer-rebuild-canonical-1', 'outer-actual-canonical-1'])))
write('selected-constructed-strict.json', [
    'outer-actual-kernels-6', 'outer-edge-kernels-3', 'outer-rebuild-kernels-3'])
write('selected-audit.json', {'name': 'full-audit-1', 'jobs': 3256, 'dependency_checks': 71215})
write('selection-status.json', {'finalized': True, 'status': 'FINAL'})
write('raw-log-archives.json', [])
write('upstream-refresh.json', {
    'command': ['git', 'pull', '--ff-only'], 'exit_code': 0,
    'output': 'From github.com:TharkunAB/cfta\n   d2fdc5ac..d65cbdb9  improve/specftacular-correctness-memory -> origin/improve/specftacular-correctness-memory\nAlready up to date.\n',
    'recorded_from_completed_call': True,
    'starting_head': (HERE / 'starting-head.txt').read_text().strip(),
    'main': subprocess.check_output(['git', 'rev-parse', 'origin/main'], cwd=ROOT, text=True).strip(),
    'formalize': subprocess.check_output(['git', 'rev-parse', 'origin/formalize'], cwd=ROOT, text=True).strip(),
    'publication': 'Pending direct approval. No push attempted.'})
components = ['outer-edge-manifest.json', 'outer-rebuild-manifest.json',
              'outer-actual-manifest.json', 'outer-cross-review-manifest.json',
              'actual-cross-manifest.json', 'root-scope-manifest.json']
write('component-manifests.json', components)
paths = [HERE / name for name in [
    'root-scope-review.md', 'root-peaks.txt', 'root-run-check.py', 'root-capped-worker.py',
    'verify-probes.py', 'verify-checkpoint.py', 'verify-preservation.py', 'verify-closure.py',
    'package-generator.py', 'current-notes-generator.py', 'current-body.txt', 'proof-commit.txt']]
for path in HERE.iterdir():
    if path.is_file() and path.name.startswith((
            'outer-schedule-', 'outer-actual-kernels', 'outer-actual-claim', 'full-audit-')):
        paths.append(path)
for name in names + [
    'SourceCurrentParentUniformGuardAlphabet', 'SourceCurrentParentUniformEnvelope',
    'SourceCurrentParentInitialRoom', 'SourceCurrentParentAlphabetReservation',
    'SourceCurrentAllocatedPartialWorker', 'SourceCurrentAllocatedPartialGraph',
    'SourceCurrentAllocatedPartialMemoSound', 'SourceCurrentAllocatedPartialInvariant',
    'SourceCurrentInheritedNumeric', 'SourceCurrentRawRebuildNumeric',
    'SourceCurrentOuterConstructorBounds', 'SourceCurrentAllocatedPartialWalkLanguage',
    'SourceCurrentAllocatedPartialForestLanguage', 'SourceCurrentAllocatedPartialCallSteps',
    'SourceCurrentMuReconstructionEffects']:
    paths.append(ROOT / 'lean/MicroCFTA' / (name + '.lean'))
write('root-scope-manifest.json', {
    'component': 'root-scope-review', 'entries': [
        {'path': str(path.relative_to(ROOT)), 'bytes': path.stat().st_size, 'sha256': sha(path)}
        for path in sorted(set(paths))]})
print(json.dumps({
    'root_scope_entries': len(set(paths)),
    'public_pairs': sum(group['pairs'] for group in groups if group['kind'] == 'new-public'),
    'constructed_pairs': sum(group['pairs'] for group in groups if group['kind'] == 'constructed'),
    'private_claim_pairs': sum(group['pairs'] for group in groups if group['kind'] == 'private-claim')}))
