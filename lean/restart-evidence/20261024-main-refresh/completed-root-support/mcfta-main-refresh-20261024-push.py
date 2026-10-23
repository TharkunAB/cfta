import hashlib
import json
import subprocess
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
here = root / 'lean/restart-evidence/20261024-main-refresh'
start = 'd501c53489b4ba9a41fd178c7ccdd0bf530dcde7'
def git(*args):
    return subprocess.check_output(['git', *args], cwd=root, text=True)
publication = json.loads(Path('/tmp/mcfta-main-refresh-20261024-local-publication.json').read_bytes())
assert publication['status'] == 'LOCAL_PASS' and publication['filesystem_index_HEAD_equal']
head = git('rev-parse', 'HEAD').strip()
assert head == publication['checkpoint'] and not git('status', '--porcelain')
assert git('branch', '--show-current').strip() == 'formalize'
assert git('rev-list', '--count', start + '..HEAD').strip() == '139'
for option in [[], ['--push']]:
    assert git('remote', 'get-url', *option, 'origin').strip() == 'git@github.com:TharkunAB/cfta.git'
for line in (here / 'SHA256SUMS').read_text().splitlines():
    digest, name = line.split('  ', 1)
    assert hashlib.sha256((here / name).read_bytes()).hexdigest() == digest
command = ['git', '-c', 'url.https://github.com/.insteadOf=git@github.com:',
           '-c', 'credential.helper=', '-c', 'credential.helper=!/snap/bin/gh auth git-credential']
def remote():
    result = subprocess.check_output(command + ['ls-remote', 'origin', 'refs/heads/formalize'], cwd=root, text=True)
    digest, reference = result.split()
    assert reference == 'refs/heads/formalize'
    return digest
assert remote() == start
subprocess.run(command + ['push', 'origin', 'HEAD:refs/heads/formalize'], cwd=root, check=True)
assert remote() == head
report = dict(status='PUSHED_AND_REMOTE_VERIFIED', branch='formalize',
              destination='git@github.com:TharkunAB/cfta.git', previous=start,
              checkpoint=head, imported_main='6b62b4afefca80bb05f5a37546212a99980aa3df',
              negative_depth_fix='058b11fe8f3706460156d7a1fc454063406a4634',
              open_LPO_repairs=2, full_goal_complete=False)
Path('/tmp/mcfta-main-refresh-20261024-remote-publication.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report))
