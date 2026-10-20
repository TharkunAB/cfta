import datetime,json,subprocess
from pathlib import Path
root=Path('/home/tritlo/Code/mcfta')
here=root/'lean/restart-evidence/20261020-native-original-indexed-resumption'
def git(*args):return subprocess.check_output(['git',*args],cwd=root,text=True)
assert not git('status','--porcelain')
head=git('rev-parse','HEAD').strip()
tracked=set(git('ls-files').splitlines())
for line in (here/'SHA256SUMS').read_text().splitlines():assert line.split('  ',1)[1] in tracked
with Path('/tmp/mcfta-native-indexed-push.log').open('xb') as log:
 push=subprocess.run(['git','push','origin','HEAD:formalize'],cwd=root,stdout=log,stderr=subprocess.STDOUT)
assert push.returncode==0,Path('/tmp/mcfta-native-indexed-push.log').read_text()
remote_text=git('ls-remote','origin','refs/heads/formalize','refs/heads/main')
Path('/tmp/mcfta-native-indexed-remote.txt').write_text(remote_text)
remote=dict(line.split()[::-1] for line in remote_text.splitlines())
assert remote['refs/heads/formalize']==head
record=dict(status='PUSHED_PENDING_CLOSURE',head=head,latest_proof=(here/'proof-commit.txt').read_text().strip(),imported_main='794903b3fbad3becb8b28736fc33463760731fc7',remote=remote,newer_upstream_main_observed=remote['refs/heads/main']!='794903b3fbad3becb8b28736fc33463760731fc7',push_exit_code=push.returncode,goal_status='active',observed_at=datetime.datetime.now(datetime.timezone.utc).isoformat())
Path('/tmp/mcfta-native-indexed-publication.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record,indent=2))
