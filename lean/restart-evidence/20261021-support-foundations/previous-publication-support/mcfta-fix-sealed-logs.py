import hashlib
import json
import os
import shutil
import subprocess
from pathlib import Path

ROOT = Path('/home/tritlo/Code/mcfta')
HERE = ROOT / 'lean/restart-evidence/20261021-sealed-log-publication'
HERE.mkdir(exist_ok=True)


def git(*args):
    return subprocess.check_output(['git', *args], cwd=ROOT)


assert git('rev-parse', 'HEAD').decode().strip() == 'b49c1079c8b72fb707f43d8ec19bf4da5f6cbf6f'
assert not git('diff', '--name-only')
report = json.loads(Path('/tmp/mcfta-sealed-log-audit.json').read_text())
assert report['status'] == 'PASS' and not report['missing_local']
names = sorted(report['required_untracked_files'])
assert len(names) == 77
for name in names:
    assert name.endswith('.log')
    assert name.startswith(('lean/restart-evidence/20261021-outer-plain-owner/',
                            'lean/restart-evidence/20261021-selected-owner-history/'))
    data = (ROOT / name).read_bytes()
    assert hashlib.sha256(data).hexdigest() == report['required_untracked_files'][name]['sha256']
for pattern in ['mcfta-sealed-log-audit.py', 'mcfta-sealed-log-audit.json',
                'mcfta-sealed-log-audit-1.*', 'mcfta-sealed-log-audit-2.*',
                'mcfta-sealed-log-fix-1.*']:
    for path in Path('/tmp').glob(pattern):
        if path.is_file():
            shutil.copyfile(path, HERE / path.name)
(HERE / 'README.md').write_text('''# Publish required sealed validation logs

The repository ignores *.log. Two recent publication commands added their
restart directories without forcing those files. Their local checksum
seals passed, but 77 required logs were absent from the branch.
The logs contain 28313077 bytes. Their existing SHA256SUMS entries match.
This change adds those exact logs. It changes no existing source or seal.
The audit reads all older checksum manifests and finds no missing local
file. The first audit read repository-relative paths incorrectly. Its
source and result remain. The second audit supports both path forms.
No Lean job is repeated for this publication correction.
Future publications must check every sealed path against the Git index.
''')
subprocess.run(['git', 'add', '-f', '--', *names], cwd=ROOT, check=True)
subprocess.run(['git', 'add', '-f', '--', str(HERE.relative_to(ROOT))], cwd=ROOT, check=True)
selected = git('diff', '--cached', '--name-status').decode().splitlines()
assert all(line.startswith('A\t') for line in selected)
assert {line[2:] for line in selected} == set(names) | {str(p.relative_to(ROOT)) for p in HERE.iterdir() if p.is_file()}
subprocess.run(['git', 'commit', '--quiet', '-m', 'Publish raw validation logs required by sealed proof checkpoints'], cwd=ROOT, check=True)
for name in names:
    assert git('show', 'HEAD:' + name) == (ROOT / name).read_bytes(), name
tracked = set(git('ls-files', '-z').decode().split('\0'))
checked = 0
for manifest in (ROOT / 'lean/restart-evidence').rglob('SHA256SUMS'):
    for line in manifest.read_text().splitlines():
        digest, name = line.split('  ', 1)
        path = ROOT / name if name.startswith('lean/') else manifest.parent / name
        relative = str(path.relative_to(ROOT))
        assert relative in tracked, relative
        checked += 1
assert not git('status', '--porcelain')
head = git('rev-parse', 'HEAD').decode().strip()
env = {**os.environ, 'GIT_SSH_COMMAND': 'ssh -p 443 -o Hostname=ssh.github.com -o HostKeyAlias=github.com -o StrictHostKeyChecking=yes -o ConnectTimeout=15 -o ConnectionAttempts=1 -o BatchMode=yes -o ServerAliveInterval=10 -o ServerAliveCountMax=2'}
with Path('/tmp/mcfta-sealed-log-fix-push.log').open('xb') as log:
    subprocess.run(['timeout', '45s', 'git', 'push', 'origin', 'HEAD:formalize'], cwd=ROOT,
                   env=env, stdout=log, stderr=subprocess.STDOUT, check=True)
remote = subprocess.check_output(['timeout', '45s', 'git', 'ls-remote', 'origin', 'refs/heads/formalize', 'refs/heads/main'], cwd=ROOT, env=env, text=True)
assert head + '\trefs/heads/formalize' in remote
assert '794903b3fbad3becb8b28736fc33463760731fc7\trefs/heads/main' in remote
result = {'status': 'PASS', 'checkpoint': head, 'proof': '50580b1d2fe6090314ba43ca2b3d6bca45d057c9',
          'added_required_logs': len(names), 'all_sealed_paths_in_index': checked,
          'clean': not bool(git('status', '--porcelain')), 'remote': remote}
Path('/tmp/mcfta-sealed-log-fix-publication.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result))
