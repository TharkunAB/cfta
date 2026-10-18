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
write('frozen-modules.json', {
    name: sha(ROOT / 'lean/MicroCFTA' / (name + '.lean')) for name in names})
groups = [
    {'name': 'edit-budget-public-1', 'pairs': 9, 'kind': 'new-public', 'full_proof': True},
    {'name': 'finite-edit-guard-public-1', 'pairs': 1, 'kind': 'new-public', 'full_proof': True},
]
selected = {name: read(name + '-selection.json') for name in
            ['edit-guard', 'edit-scan', 'class-guard', 'preparation-guard', 'outer-constructor']}
for selection in selected.values():
    for original in selection['selected_groups']:
        group = dict(original)
        if group['kind'] == 'public':
            group['kind'] = 'new-public'
        groups.append(group)
write('selected-groups.json', groups)
stricts = ['edit-guard-direct-2', 'edit-budget-direct-3', 'edit-scan-direct-3',
           'finite-edit-guard-direct-2', 'class-guard-direct-1',
           'preparation-guard-direct-2', 'outer-constructor-direct-3']
canonicals = ['edit-guard-canonical-1', 'edit-budget-canonical-1', 'edit-scan-canonical-2',
              'finite-edit-guard-canonical-1', 'class-guard-canonical-1',
              'preparation-guard-canonical-1', 'outer-constructor-canonical-2']
write('selected-strict.json', dict(zip(names, stricts)))
write('selected-canonical.json', dict(zip(names, canonicals)))
write('selected-constructed-strict.json', [
    selection.get('constructed_strict', selection.get('kernel_strict'))
    for selection in selected.values()])
write('selected-audit.json', {'name': 'full-audit-1', 'jobs': 3248, 'dependency_checks': 71103})
write('selection-status.json', {'finalized': True, 'status': 'FINAL'})
write('raw-log-archives.json', [])
write('upstream-refresh.json', {
    'command': ['git', 'pull', '--ff-only'], 'exit_code': 0,
    'output': 'From github.com:TharkunAB/cfta\n   bb2f5589..d2fdc5ac  improve/specftacular-correctness-memory -> origin/improve/specftacular-correctness-memory\nAlready up to date.\n',
    'recorded_from_completed_call': True,
    'starting_head': (HERE / 'starting-head.txt').read_text().strip(),
    'main': 'c0cc8a0582cd6b01c344ec15f949ecb46a72dc0e',
    'formalize': 'a1270b81422ea48ffe0a84f2c774e6c7c1f86b0a',
    'publication': 'Pending direct approval. No push attempted.'})
components = [name + '-manifest.json' for name in selected]
components += ['editor-cross-review-manifest.json', 'root-scope-manifest.json']
write('component-manifests.json', components)
paths = [HERE / name for name in [
    'root-scope-review.md', 'root-peaks.txt', 'root-run-check.py', 'root-capped-worker.py',
    'verify-probes.py', 'verify-checkpoint.py', 'verify-preservation.py', 'verify-closure.py',
    'package-generator.py', 'current-notes-generator.py', 'current-body.txt', 'proof-commit.txt']]
for path in HERE.iterdir():
    if path.is_file() and path.name.startswith(('edit-budget-', 'finite-edit-guard-', 'full-audit-')):
        paths.append(path)
for name in names + [
    'SourceCurrentClassesNumeric', 'SourceCurrentClassesForecast',
    'SourceCurrentScanNumericForecast', 'SourceCurrentScanRequiredForecast',
    'SourceCurrentInitialSelectionForecast', 'SourceCurrentLocalNumeric',
    'SourceCurrentParentNumeric', 'SourceCurrentParentUniformEnvelope',
    'SourceCurrentOuterCallBudget', 'SourceCurrentRequiredHeapEffects']:
    paths.append(ROOT / 'lean/MicroCFTA' / (name + '.lean'))
write('root-scope-manifest.json', {
    'component': 'root-scope-review', 'entries': [
        {'path': str(path.relative_to(ROOT)), 'bytes': path.stat().st_size, 'sha256': sha(path)}
        for path in sorted(set(paths))]})
print(json.dumps({
    'root_scope_entries': len(set(paths)),
    'public_pairs': sum(group['pairs'] for group in groups if group['kind'] == 'new-public'),
    'constructed_pairs': sum(group['pairs'] for group in groups if group['kind'] == 'constructed')}))
