import datetime
import json
import subprocess
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
here = root / 'lean/restart-evidence/20261023-original-row-reconstruction'
def git(*args):
    return subprocess.check_output(['git', *args], cwd=root, text=True).strip()

publication = json.loads(Path('/tmp/mcfta-original-row-reconstruction-local-publication.json').read_bytes())
assert publication['status'] == 'LOCAL_PASS'
head = git('rev-parse', 'HEAD')
proof = (here / 'proof-commit.txt').read_text().strip()
start = (here / 'starting-head.txt').read_text().strip()
assert git('branch', '--show-current') == 'formalize'
assert head == publication['checkpoint'] and proof == publication['proof']
assert git('rev-parse', head + '^') == proof and git('rev-parse', proof + '^') == start
assert git('rev-list', '--count', start + '..' + head) == '2'
assert not git('status', '--porcelain')
destination = git('remote', 'get-url', '--push', 'origin')
assert destination == 'git@github.com:TharkunAB/cfta.git'
ref = 'refs/heads/formalize'
before = git('ls-remote', 'origin', ref).split()
assert before == [start, ref], before
subprocess.run(['git', 'push', 'origin', 'HEAD:' + ref], cwd=root, check=True)
after = git('ls-remote', 'origin', ref).split()
assert after == [head, ref], after
assert git('rev-parse', 'origin/formalize') == head and not git('status', '--porcelain')
report = dict(status='PUSHED_AND_REMOTE_VERIFIED', observed_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    destination=destination, ref=ref, before=start, proof_commit=proof, checkpoint=head, commits=2,
    authorization='Explicit user authorization to push to the formalize branch.', clean=True)
path = Path('/tmp/mcfta-original-row-reconstruction-authorized-push.json')
assert not path.exists()
path.write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report))
