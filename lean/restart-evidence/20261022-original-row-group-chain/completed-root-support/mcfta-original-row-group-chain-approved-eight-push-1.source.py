import datetime
import json
import os
import subprocess
from pathlib import Path

ROOT = Path('/home/tritlo/Code/mcfta')
BASE = '562120d456ea5836dc0f3cc718dafd25323521c3'
FIRST = '2cc495ab5e39ae603880acd56f17122595242699'
TIP = 'd0cf685f461430a7c608ceb3b76da0fe568e4d84'
DESTINATION = 'git@github.com:TharkunAB/cfta.git'
REF = 'refs/heads/formalize'
def git(*args):
    return subprocess.check_output(['git', *args], cwd=ROOT, text=True).strip()

assert git('branch', '--show-current') == 'formalize'
assert git('remote', 'get-url', '--push', 'origin') == DESTINATION
assert not git('diff', '--cached', '--name-only')
head = git('rev-parse', 'HEAD')
commits = git('rev-list', '--reverse', BASE + '..' + TIP).splitlines()
assert len(commits) == 8 and commits[0] == FIRST and commits[-1] == TIP
subprocess.run(['git', 'merge-base', '--is-ancestor', TIP, head], cwd=ROOT, check=True)
env = dict(os.environ, GIT_SSH_COMMAND='ssh -p 443 -o Hostname=ssh.github.com -o HostKeyAlias=github.com -o StrictHostKeyChecking=yes -o ConnectTimeout=15 -o ConnectionAttempts=1 -o BatchMode=yes -o ServerAliveInterval=10 -o ServerAliveCountMax=2')
def remote_tip():
    raw = subprocess.check_output(['git', 'ls-remote', '--exit-code', DESTINATION, REF], cwd=ROOT, env=env, text=True, timeout=45)
    commit, ref = raw.strip().split()
    assert ref == REF
    return commit

before = remote_tip()
assert before in {BASE, TIP}, before
log = Path('/tmp/mcfta-original-row-cluster-approved-push.network.log')
assert not log.exists()
with log.open('x') as output:
    result = subprocess.run(['git', 'push', 'origin', TIP + ':' + REF], cwd=ROOT, env=env, stdout=output, stderr=subprocess.STDOUT, timeout=180)
assert result.returncode == 0, log.read_text()
after = remote_tip()
assert after == TIP
assert git('rev-parse', 'HEAD') == head
receipt = dict(status='PUSHED_AND_REMOTE_VERIFIED', observed_at=datetime.datetime.now().astimezone().isoformat(),
    approval='Direct user reply: Approve this exact push', approval_question_call='call_9d71f30f8cf54c798ca89c1dae9417f9',
    destination=DESTINATION, remote_branch=REF, previous_remote=before,
    approved_first=FIRST, approved_and_pushed_tip=TIP, approved_commit_count=8,
    push_exit_code=result.returncode, verified_remote_tip=after,
    local_head_unchanged=head, newer_commits_outside_this_exact_payload=git('rev-list','--count',TIP+'..'+head),
    sealed_proof_evidence_changed=False, whole_goal_complete=False)
path = Path('/tmp/mcfta-original-row-cluster-approved-push.json')
assert not path.exists()
path.write_text(json.dumps(receipt, indent=2) + '\n')
print(json.dumps(receipt))
