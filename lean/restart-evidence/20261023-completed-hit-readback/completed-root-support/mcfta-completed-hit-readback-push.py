import datetime
import json
import os
import subprocess
from pathlib import Path

ROOT = Path('/home/tritlo/Code/mcfta')
HERE = ROOT / 'lean/restart-evidence/20261023-completed-hit-readback'
def git(*args):
    return subprocess.check_output(['git', *args], cwd=ROOT, text=True).strip()

publication = json.loads(Path('/tmp/mcfta-completed-hit-readback-local-publication.json').read_text())
assert publication['status'] == 'LOCAL_PASS'
head = git('rev-parse', 'HEAD')
proof = (HERE / 'proof-commit.txt').read_text().strip()
start = (HERE / 'starting-head.txt').read_text().strip()
assert git('branch', '--show-current') == 'formalize'
assert head == publication['checkpoint'] and proof == publication['proof']
assert git('rev-parse', head + '^') == proof and git('rev-parse', proof + '^') == start
assert git('rev-list', '--count', start + '..' + head) == '2'
assert not git('status', '--porcelain')
destination = git('remote', 'get-url', '--push', 'origin')
assert destination == 'git@github.com:TharkunAB/cfta.git'
ref = 'refs/heads/formalize'
https = ['-c', 'url.https://github.com/.insteadOf=git@github.com:']
env = dict(os.environ, GIT_TERMINAL_PROMPT='0',
    GIT_SSH_COMMAND='ssh -o BatchMode=yes -o ConnectTimeout=10 -o ConnectionAttempts=1')
def remote():
    return subprocess.check_output(['git', *https, 'ls-remote', 'origin', ref],
        cwd=ROOT, env=env, text=True, timeout=45).split()

assert remote() == [start, ref]
attempts = []
for transport, options in [('ssh', []), ('https', https)]:
    path = Path('/tmp/mcfta-completed-hit-readback-push-' + transport + '.log')
    with path.open('xb') as log:
        result = subprocess.run(['git', *options, 'push', 'origin', 'HEAD:' + ref],
            cwd=ROOT, env=env, stdout=log, stderr=subprocess.STDOUT, timeout=90)
    attempts.append(dict(transport=transport, exit_code=result.returncode, log=str(path)))
    actual = remote()
    if actual == [head, ref]:
        break
    assert actual == [start, ref], actual
    assert result.returncode != 0
else:
    raise RuntimeError('Both authorized push transports failed; the remote branch is unchanged.')
assert remote() == [head, ref]
assert git('rev-parse', 'origin/formalize') == head and not git('status', '--porcelain')
report = dict(status='PUSHED_AND_REMOTE_VERIFIED', observed_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    destination=destination, ref=ref, before=start, proof_commit=proof, checkpoint=head, commits=2,
    authorization='Explicit user authorization to push to the formalize branch.', clean=True, attempts=attempts)
path = Path('/tmp/mcfta-completed-hit-readback-authorized-push.json')
assert not path.exists()
path.write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report))
