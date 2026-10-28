from pathlib import Path
import json,os,subprocess,sys
root=Path('/home/tritlo/Code/mcfta');area=Path('/tmp/mcfta-prepared-models-20261028');destination='git@github.com:TharkunAB/cfta.git';branch='refs/heads/formalize'
env=dict(os.environ,GIT_SSH_COMMAND='ssh -o ConnectTimeout=15 -o ConnectionAttempts=1 -o BatchMode=yes -o StrictHostKeyChecking=yes -o HostKeyAlias=github.com -o Hostname=ssh.github.com -p443')
def git(*args,network=False):return subprocess.check_output(['git',*args],cwd=root,env=env if network else None,stderr=subprocess.STDOUT)
source='--source' in sys.argv
assert git('branch','--show-current').decode().strip()=='formalize'
assert git('remote','get-url','origin').decode().strip()==destination
head=git('rev-parse','HEAD').decode().strip();base=(area/'published-base.txt').read_text().strip()
if source:assert head==(area/'source-head.txt').read_text().strip()
else:assert not git('status','--porcelain=v1','-z')
assert git('merge-base',base,head).decode().strip()==base
payload=git('rev-list','--reverse',base+'..HEAD').decode().splitlines();assert payload
record=dict(destination=destination,branch=branch,head=head,published_base=base,commits=payload,source_publication=source)
suffix='source-' if source else ''
Path('/tmp/mcfta-prepared-models-'+suffix+'push-request.json').write_text(json.dumps(record,indent=2)+'\n')
record['push_output']=git('push',destination,'HEAD:'+branch,network=True).decode();record['remote_head']=git('ls-remote',destination,branch,network=True).decode().split()[0]
record['fetch_output']=git('fetch','origin','formalize',network=True).decode();record['tracking_head']=git('rev-parse','refs/remotes/origin/formalize').decode().strip();record['clean']=not git('status','--porcelain=v1','-z')
assert record['remote_head']==record['tracking_head']==head
if not source:assert record['clean']
Path('/tmp/mcfta-prepared-models-'+suffix+'publication.json').write_text(json.dumps(record,indent=2)+'\n');print(json.dumps(record))
