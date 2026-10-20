import json,shutil
from pathlib import Path
here=Path('/home/tritlo/Code/mcfta/lean/restart-evidence/20261020-native-original-captured-node-rows')
for ext in ['json','log','limits.json','peaks.txt','source.py','usage.json']:
    shutil.copyfile('/tmp/mcfta-captured-bootstrap-1.'+ext,here/('bootstrap-run.'+ext))
for stem,target in [('mcfta-node-finalize-1','previous-finalize'),('mcfta-node-closure-1','previous-closure')]:
    for ext in ['json','log','limits.json','peaks.txt','source.py','usage.json']:
        shutil.copyfile('/tmp/'+stem+'.'+ext,here/(target+'.'+ext))
for source,target in [('mcfta-native-node-publication.json','previous-publication.json'),('mcfta-native-node-push.log','previous-push.log'),('mcfta-native-node-remote.txt','previous-remote.txt'),('mcfta-native-node-board-readback.json','previous-board-readback.json')]:
    shutil.copyfile('/tmp/'+source,here/target)
refresh={'pull_exit_code':0,'command':['git','pull','--ff-only'],'transport':'ssh port 443','ssh_command':'ssh -p 443 -o Hostname=ssh.github.com -o HostKeyAlias=github.com -o StrictHostKeyChecking=yes -o ConnectTimeout=10 -o ConnectionAttempts=1 -o BatchMode=yes -o ServerAliveInterval=5 -o ServerAliveCountMax=2','timeout_seconds':35,'root_observed_handle':97546,'output':'Already up to date.\n','main':'794903b3fbad3becb8b28736fc33463760731fc7','formalize':'499357bf4fe4bc50c9183271f028dd43d21e475e','this_checkpoint_imported_changes':False,'observed_at':'2026-10-20 23:35 CEST','backup_branch':'codex/backup-captured-node-origins-20261020-2328','earlier_attempts':[{'handle':41130,'transport':'ssh port 22','result':'Exact stalled SSH child terminated after over five minutes. Git reported remote read failure. Later harmless commands made the combined shell exit zero. This is not a successful pull.'},{'handle':27099,'transport':'ssh port 22 with bounded connection timeout','exit_code':1,'output':'ssh: connect to host github.com port 22: Connection timed out\r\nfatal: Could not read from remote repository.\n\nPlease make sure you have the correct access rights\nand the repository exists.\n'},{'handle':58013,'transport':'https','timeout_seconds':55,'exit_code':124,'output':''}]}
(here/'upstream-refresh.json').write_text(json.dumps(refresh,indent=2)+'\n')
print(json.dumps({'status':'PASS','previous_checkpoint':'499357bf4','pull_exit_code':0}))
