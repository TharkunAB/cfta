import hashlib
import json
import subprocess
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
here = root / 'lean/restart-evidence/20261024-main-refresh'
def git(*args):
    return subprocess.check_output(['git', *args], cwd=root)
assert git('rev-parse', 'HEAD').decode().strip() == '058b11fe8f3706460156d7a1fc454063406a4634'
assert git('branch', '--show-current').decode().strip() == 'formalize'
result = subprocess.run(['/usr/bin/python3', str(here / 'verify-preservation.py')],
                        cwd='/', capture_output=True, text=True)
(here / 'preservation-final.stderr').write_text(result.stderr)
assert result.returncode == 0, result.stdout + result.stderr
preserved = json.loads(result.stdout)
assert preserved['status'] == 'PASS'
(here / 'preservation-final.json').write_text(json.dumps(preserved, indent=2) + '\n')
documents = list(json.loads((here / 'document-changes.json').read_bytes()))
documents.append('lean/notes-current-upstream-program-enumeration.md')
scope = {name: hashlib.sha256((root / name).read_bytes()).hexdigest() for name in documents}
(here / 'document-scope.json').write_text(json.dumps(scope, indent=2) + '\n')
files = sorted(path for path in here.rglob('*') if path.is_file())
assert not (here / 'SHA256SUMS').exists()
(here / 'SHA256SUMS').write_text(''.join(hashlib.sha256(path.read_bytes()).hexdigest() + '  ' + str(path.relative_to(here)) + '\n' for path in files))
subprocess.run(['git', 'diff', '--check'], cwd=root, check=True)
subprocess.run(['git', 'add', '-f', '--', *documents, str(here.relative_to(root))], cwd=root, check=True)
staged = git('diff', '--cached', '--name-only').decode().splitlines()
assert all(name in documents or name.startswith(str(here.relative_to(root)) + '/') for name in staged)
subprocess.run(['git', 'commit', '--quiet', '-m', 'Record upstream enumeration changes and formalization gaps'], cwd=root, check=True)
head = git('rev-parse', 'HEAD').decode().strip()
assert not git('status', '--porcelain')
tree = {}
for raw in git('ls-tree', '-r', '-z', 'HEAD').split(b'\0'):
    if not raw:
        continue
    meta, name = raw.split(b'\t', 1)
    mode, kind, blob = meta.decode().split()
    assert kind == 'blob'
    path = root / name.decode()
    data = path.read_bytes()
    assert hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest() == blob, name
    assert ('100755' if path.stat().st_mode & 0o111 else '100644') == mode, name
    tree[name.decode()] = (mode, blob)
index = {}
for raw in git('ls-files', '--stage', '-z').split(b'\0'):
    if not raw:
        continue
    meta, name = raw.split(b'\t', 1)
    mode, blob, stage = meta.decode().split()
    assert stage == '0'
    index[name.decode()] = (mode, blob)
assert tree == index
for line in (here / 'SHA256SUMS').read_text().splitlines():
    digest, name = line.split('  ', 1)
    assert hashlib.sha256((here / name).read_bytes()).hexdigest() == digest
report = dict(status='LOCAL_PASS', checkpoint=head, tracked_files_and_modes=len(tree),
              clean=True, filesystem_index_HEAD_equal=True, preserved=preserved,
              network_commands=0, push='AUTHORIZED_PENDING')
Path('/tmp/mcfta-main-refresh-20261024-local-publication.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps({key: value for key, value in report.items() if key != 'preserved'}))
