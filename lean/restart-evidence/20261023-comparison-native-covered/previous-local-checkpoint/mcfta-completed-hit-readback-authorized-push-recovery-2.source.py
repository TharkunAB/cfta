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
https += ['-c', 'credential.helper=', '-c', 'credential.helper=!/snap/bin/gh auth git-credential']
env = dict(os.environ, GIT_TERMINAL_PROMPT='0')
previous = Path('/tmp/mcfta-completed-hit-readback-authorized-push-1.log')
assert 'subprocess.TimeoutExpired' in previous.read_text()
attempts = [dict(transport='ssh', status='TIMED_OUT', timeout_seconds=90,
    receipt='/tmp/mcfta-completed-hit-readback-authorized-push-1.json', log=str(previous))]
failed_https = Path('/tmp/mcfta-completed-hit-readback-push-recovery-https.log')
assert "could not read Username for 'https://github.com'" in failed_https.read_text()
attempts.append(dict(transport='https', status='CREDENTIAL_HELPER_MISSING',
    receipt='/tmp/mcfta-completed-hit-readback-authorized-push-recovery-1.json', log=str(failed_https)))

def remote():
    return subprocess.check_output(['git', *https, 'ls-remote', 'origin', ref],
        cwd=ROOT, env=env, text=True, timeout=35).split()

before = remote()
assert before in ([start, ref], [head, ref]), before
if before == [start, ref]:
    path = Path('/tmp/mcfta-completed-hit-readback-push-recovery-gh-https.log')
    with path.open('xb') as log:
        try:
            result = subprocess.run(['git', *https, 'push', 'origin', 'HEAD:' + ref],
                cwd=ROOT, env=env, stdout=log, stderr=subprocess.STDOUT, timeout=150)
            attempts.append(dict(transport='https', credential_helper='Existing gh login', exit_code=result.returncode, log=str(path)))
        except subprocess.TimeoutExpired:
            attempts.append(dict(transport='https', status='TIMED_OUT', timeout_seconds=150, log=str(path)))
    assert remote() == [head, ref]
else:
    attempts.append(dict(transport='https', status='NO_PUSH_NEEDED_REMOTE_ALREADY_MATCHES'))
tracking = git('rev-parse', 'origin/formalize')
assert tracking in (start, head)
if tracking != head:
    git('update-ref', 'refs/remotes/origin/formalize', head, start)
assert remote() == [head, ref]
assert git('rev-parse', 'origin/formalize') == head and not git('status', '--porcelain')
report = dict(status='PUSHED_AND_REMOTE_VERIFIED', observed_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    destination=destination, ref=ref, before=start, proof_commit=proof, checkpoint=head, commits=2,
    authorization='Explicit user authorization to push to the formalize branch.', clean=True, attempts=attempts)
path = Path('/tmp/mcfta-completed-hit-readback-authorized-push.json')
assert not path.exists()
path.write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report))
