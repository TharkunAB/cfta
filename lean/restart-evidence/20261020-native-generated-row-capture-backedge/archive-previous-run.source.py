import json,shutil
from pathlib import Path
here=Path('/home/tritlo/Code/mcfta/lean/restart-evidence/20261020-native-generated-row-capture-backedge')
for ext in ['json','log','limits.json','peaks.txt','source.py','usage.json']:
    shutil.copyfile('/tmp/mcfta-backedge-bootstrap-1.'+ext,here/('bootstrap-run.'+ext))
for stem,target in [('mcfta-captured-finalize-1','previous-finalize'),('mcfta-captured-closure-1','previous-closure')]:
    for ext in ['json','log','limits.json','peaks.txt','source.py','usage.json']:
        shutil.copyfile('/tmp/'+stem+'.'+ext,here/(target+'.'+ext))
for source,target in [('mcfta-native-captured-publication.json','previous-publication.json'),('mcfta-native-captured-push.log','previous-push.log'),('mcfta-native-captured-remote.txt','previous-remote.txt'),('mcfta-native-captured-board-readback.json','previous-board-readback.json')]:
    shutil.copyfile('/tmp/'+source,here/target)
refresh=dict(pull_exit_code=0,command=['git','pull','--ff-only'],transport='ssh port 443',ssh_command='ssh -p 443 -o Hostname=ssh.github.com -o HostKeyAlias=github.com -o StrictHostKeyChecking=yes -o ConnectTimeout=15 -o ConnectionAttempts=1 -o BatchMode=yes -o ServerAliveInterval=10 -o ServerAliveCountMax=2',timeout_seconds=45,root_observed_handle=30262,output='Already up to date.\n',main='794903b3fbad3becb8b28736fc33463760731fc7',formalize='0dab9a59db6800007041371af7adea8c4898274d',this_checkpoint_imported_changes=False,observed_at='2026-10-20 23:47 CEST',backup_branch='codex/backup-generated-row-capture-20261020-2347')
(here/'upstream-refresh.json').write_text(json.dumps(refresh,indent=2)+'\n')
print(json.dumps({'status':'PASS','previous_checkpoint':'0dab9a59d','pull_exit_code':0}))
