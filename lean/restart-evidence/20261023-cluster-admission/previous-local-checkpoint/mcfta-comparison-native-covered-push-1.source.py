import datetime
import json
import subprocess
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
start = 'b796e8e660a73ac328d41cad53c61099ba79d93f'
report = json.loads(Path('/tmp/mcfta-comparison-native-covered-local-publication.json').read_text())
assert report['status'] == 'LOCAL_PASS' and report['filesystem_index_head_equal'] and report['clean']
def git(*args):
    return subprocess.check_output(['git', *args], cwd=root, text=True).strip()
assert git('branch', '--show-current') == 'formalize'
assert git('remote', 'get-url', 'origin') == 'git@github.com:TharkunAB/cfta.git'
assert not git('status', '--porcelain')
head = git('rev-parse', 'HEAD')
assert head == report['checkpoint']
assert git('rev-parse', 'HEAD~2') == start
assert git('rev-parse', 'HEAD~1') == report['proof']
network = ['git', '-c', 'url.https://github.com/.insteadOf=git@github.com:',
    '-c', 'credential.helper=', '-c', 'credential.helper=!/snap/bin/gh auth git-credential']
def remote_tip():
    rows = subprocess.check_output([*network, 'ls-remote', 'origin', 'refs/heads/formalize'], cwd=root, text=True).splitlines()
    assert len(rows) == 1
    value, ref = rows[0].split()
    assert ref == 'refs/heads/formalize'
    return value
before = remote_tip()
assert before == start, before
subprocess.run([*network, 'push', 'origin', 'HEAD:refs/heads/formalize'], cwd=root, check=True)
after = remote_tip()
assert after == head == git('rev-parse', 'origin/formalize')
assert not git('status', '--porcelain')
receipt = dict(status='PUSHED_AND_REMOTE_VERIFIED', branch='formalize',
    destination='git@github.com:TharkunAB/cfta.git', transport='HTTPS with existing gh credential helper; per-command configuration only',
    before=before, proof=report['proof'], checkpoint=head, remote_tip=after, tracking_tip=git('rev-parse', 'origin/formalize'),
    clean=True, force=False, user_authorization='Keep going. You are explicitly authorized to push to the formalize branch',
    observed_at=datetime.datetime.now().astimezone().isoformat())
path = Path('/tmp/mcfta-comparison-native-covered-authorized-push.json')
assert not path.exists()
path.write_text(json.dumps(receipt, indent=2) + '\n')
print(json.dumps(receipt))
