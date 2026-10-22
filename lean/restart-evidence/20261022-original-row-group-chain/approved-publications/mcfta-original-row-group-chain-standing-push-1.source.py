import datetime
import json
import os
import subprocess
from pathlib import Path

ROOT = Path('/home/tritlo/Code/mcfta')
BASE = 'd0cf685f461430a7c608ceb3b76da0fe568e4d84'
TIP = '70787b95484cb69897bc4075858e07c7f9c22433'
DESTINATION = 'git@github.com:TharkunAB/cfta.git'
REF = 'refs/heads/formalize'
def git(*args):
    return subprocess.check_output(['git', *args], cwd=ROOT, text=True).strip()

publication = json.loads(Path('/tmp/mcfta-prepend-grouping-local-publication.json').read_text())
assert publication['status'] == 'LOCAL_PASS' and publication['checkpoint'] == TIP
assert publication['filesystem_index_head_equal'] and publication['clean']
assert publication['tracked_blobs_and_modes'] == 96320
assert git('branch', '--show-current') == 'formalize'
assert git('rev-parse', 'HEAD') == TIP
assert git('remote', 'get-url', '--push', 'origin') == DESTINATION
assert not git('diff', '--name-only') and not git('diff', '--cached', '--name-only')
assert git('rev-list', '--count', BASE + '..' + TIP) == '2'
env = dict(os.environ, GIT_SSH_COMMAND='ssh -p 443 -o Hostname=ssh.github.com -o HostKeyAlias=github.com -o StrictHostKeyChecking=yes -o ConnectTimeout=15 -o ConnectionAttempts=1 -o BatchMode=yes -o ServerAliveInterval=10 -o ServerAliveCountMax=2')
def remote_tip():
    raw = subprocess.check_output(['git', 'ls-remote', '--exit-code', DESTINATION, REF], cwd=ROOT, env=env, text=True, timeout=45)
    commit, ref = raw.strip().split()
    assert ref == REF
    return commit

before = remote_tip()
assert before in {BASE, TIP}
log = Path('/tmp/mcfta-prepend-grouping-authorized-push.network.log')
assert not log.exists()
with log.open('x') as output:
    result = subprocess.run(['git', 'push', 'origin', TIP + ':' + REF], cwd=ROOT, env=env, stdout=output, stderr=subprocess.STDOUT, timeout=180)
assert result.returncode == 0, log.read_text()
after = remote_tip()
assert after == TIP and git('rev-parse','HEAD') == TIP
receipt = dict(status='PUSHED_AND_REMOTE_VERIFIED', observed_at=datetime.datetime.now().astimezone().isoformat(),
    approval='Keep going. You are explicitly authorized to push to the formalize branch',
    destination=DESTINATION, remote_branch=REF, previous_remote=before, pushed_tip=TIP,
    new_commit_count=2, proof_commit=publication['proof'], verified_remote_tip=after,
    push_exit_code=result.returncode, sealed_proof_evidence_changed=False, whole_goal_complete=False)
path = Path('/tmp/mcfta-prepend-grouping-authorized-push.json')
assert not path.exists()
path.write_text(json.dumps(receipt, indent=2) + '\n')
print(json.dumps(receipt))
