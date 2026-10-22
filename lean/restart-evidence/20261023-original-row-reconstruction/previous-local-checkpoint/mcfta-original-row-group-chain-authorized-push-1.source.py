import datetime
import json
import os
import subprocess
import sys
from pathlib import Path

ROOT = Path('/home/tritlo/Code/mcfta')
BASE = '70787b95484cb69897bc4075858e07c7f9c22433'
DESTINATION = 'git@github.com:TharkunAB/cfta.git'
REF = 'refs/heads/formalize'
tip = sys.argv[1]
assert len(tip) == 40 and set(tip) <= set('0123456789abcdef')
def git(*args):
    return subprocess.check_output(['git',*args],cwd=ROOT,text=True).strip()

local = json.loads(Path('/tmp/mcfta-original-row-group-chain-local-publication.json').read_text())
assert local['status'] == 'LOCAL_PASS' and local['checkpoint'] == tip
assert local['publication'] == 'AUTHORIZED_PENDING_ROOT_PUSH'
assert local['filesystem_index_head_equal'] and local['clean']
assert local['selected_proof']['status'] == local['preservation']['status'] == 'PASS'
assert git('branch','--show-current') == 'formalize' and git('rev-parse','HEAD') == tip
assert git('remote','get-url','--push','origin') == DESTINATION
assert git('status','--porcelain') == ''
assert git('rev-list','--count',BASE+'..'+tip) == '2'
env = dict(os.environ,GIT_SSH_COMMAND='ssh -p 443 -o Hostname=ssh.github.com -o HostKeyAlias=github.com -o StrictHostKeyChecking=yes -o ConnectTimeout=15 -o ConnectionAttempts=1 -o BatchMode=yes -o ServerAliveInterval=10 -o ServerAliveCountMax=2')
def remote_tip():
    commit, ref = subprocess.check_output(['git','ls-remote','--exit-code',DESTINATION,REF],cwd=ROOT,env=env,text=True,timeout=45).strip().split()
    assert ref == REF
    return commit

before = remote_tip()
assert before in {BASE,tip},before
log = Path('/tmp/mcfta-original-row-group-chain-authorized-push.network.log')
assert not log.exists()
with log.open('x') as output:
    result = subprocess.run(['git','push','origin',tip+':'+REF],cwd=ROOT,env=env,stdout=output,stderr=subprocess.STDOUT,timeout=180)
assert result.returncode == 0,log.read_text()
after = remote_tip()
assert after == tip and git('rev-parse','HEAD') == tip and not git('status','--porcelain')
report = dict(status='PUSHED_AND_REMOTE_VERIFIED',observed_at=datetime.datetime.now().astimezone().isoformat(),
    approval='Keep going. You are explicitly authorized to push to the formalize branch',
    destination=DESTINATION,remote_branch=REF,previous_remote=before,checkpoint=tip,
    proof=local['proof'],new_commit_count=2,push_exit_code=result.returncode,
    verified_remote_tip=after,clean=True,sealed_evidence_changed=False,whole_goal_complete=False)
receipt = Path('/tmp/mcfta-original-row-group-chain-authorized-push.json')
assert not receipt.exists()
receipt.write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report))
