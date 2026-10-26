from pathlib import Path
import hashlib
import json
import subprocess

root = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-native-observed-words-20261026')
run = lambda *args: subprocess.check_output(['git', *args], cwd=root)
assert run('branch', '--show-current').decode().strip() == 'formalize'
assert run('rev-parse', 'HEAD').decode().strip() == (area / 'base.txt').read_text().strip()
assert not run('diff', '--cached', '--name-only')
finals = {
    'SourceCurrentAllocatedNativeObservedWords': 'strict-observed-words-2',
    'SourceCurrentAllocatedTargetObserved': 'strict-target-observed-1',
    'SourceCurrentAllocatedTargetInitial': 'strict-target-initial-1',
    'SourceCurrentAllocatedTargetCallerObserved': 'strict-target-caller-2',
    'SourceCurrentAllocatedNativeWordBoundary': 'strict-word-boundary-1',
    'Audit': 'strict-audit-1',
}
for module, name in finals.items():
    data = (root / 'lean/MicroCFTA' / (module + '.lean')).read_bytes()
    report = json.loads((area / name / 'report.json').read_text())
    assert report['exit_code'] == 0
    assert report['source_sha256'] == hashlib.sha256(data).hexdigest()
for name in ['helper-build-3', 'aggregate-audit-1', 'public-final-1']:
    assert json.loads((area / name / 'report.json').read_text())['exit_code'] == 0
(area / 'final-strict.json').write_text(json.dumps(finals, indent=2) + '\n')
groups = [
    ('Derive native word checks from recorded execution traces', [
        'SourceCurrentAllocatedNativeObservedWords', 'SourceCurrentAllocatedTargetObserved']),
    ('Verify native query returns from initial numeric room', [
        'SourceCurrentAllocatedTargetInitial', 'SourceCurrentAllocatedTargetCallerObserved']),
    ('Preserve the boundary between raw completion and checked traces', [
        'SourceCurrentAllocatedNativeWordBoundary', 'Audit']),
]
commits = []
for message, modules in groups:
    paths = ['lean/MicroCFTA/' + name + '.lean' for name in modules]
    subprocess.run(['git', 'add', '--', *paths], cwd=root, check=True)
    assert set(run('diff', '--cached', '--name-only').decode().splitlines()) == set(paths)
    for rel in paths:
        assert run('show', ':' + rel) == (root / rel).read_bytes(), rel
    subprocess.run(['git', 'diff', '--cached', '--check'], cwd=root, check=True)
    subprocess.run(['git', 'commit', '-m', message], cwd=root, check=True)
    commit = run('rev-parse', 'HEAD').decode().strip()
    for rel in paths:
        assert run('show', commit + ':' + rel) == (root / rel).read_bytes(), rel
    commits.append(dict(commit=commit, message=message, paths=paths))
(area / 'source-commits.json').write_text(json.dumps(commits, indent=2) + '\n')
print(json.dumps(commits, indent=2))
