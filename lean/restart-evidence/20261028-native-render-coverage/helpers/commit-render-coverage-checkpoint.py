from pathlib import Path
import json
import subprocess

root = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-render-coverage-20261028')
snapshot = root / 'lean/restart-evidence/20261028-native-render-coverage'
assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root).decode().strip() == (area / 'source-head.txt').read_text().strip()
assert not subprocess.check_output(['git', 'diff', '--cached', '--name-only', '-z'], cwd=root)
documents = json.loads((area / 'document-paths.json').read_text())
paths = documents + [str(snapshot.relative_to(root))]
subprocess.run(['git', 'add', '--', *paths], cwd=root, check=True)
staged = {item.decode() for item in subprocess.check_output(
    ['git', 'diff', '--cached', '--name-only', '-z'], cwd=root).split(b'\0') if item}
expected = set(documents) | {str(path.relative_to(root)) for path in snapshot.rglob('*') if path.is_file()}
assert staged == expected, staged ^ expected
subprocess.run(['git', 'diff', '--cached', '--check'], cwd=root, check=True)
result = subprocess.run(['git', 'commit', '-m', 'Record native render coverage and portable restart evidence'],
    cwd=root, check=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root).decode().strip()
Path('/tmp/mcfta-render-coverage-checkpoint-commit.json').write_text(json.dumps(
    {'head': head, 'paths': len(staged), 'output': result.stdout.decode()}, indent=2) + '\n')
print(json.dumps({'head': head, 'paths': len(staged)}))
