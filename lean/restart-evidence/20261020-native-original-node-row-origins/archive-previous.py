import json,shutil
from pathlib import Path
HERE=Path(__file__).resolve().parent
for stem,label in [('mcfta-node-bootstrap','bootstrap-run'),('mcfta-indexed-finalize-1','previous-finalize'),('mcfta-indexed-publish-1','previous-publish'),('mcfta-indexed-closure-1','previous-closure')]:
 for ext in ['json','log','limits.json','peaks.txt','source.py','usage.json']:
  shutil.copyfile('/tmp/'+stem+'.'+ext,HERE/(label+'.'+ext))
for source,target in [('/tmp/mcfta-native-indexed-publication.json','previous-publication.json'),('/tmp/mcfta-native-indexed-board-readback.json','previous-board-readback.json'),('/tmp/mcfta-native-indexed-push.log','previous-push.log'),('/tmp/mcfta-native-indexed-remote.txt','previous-remote.txt')]:
 shutil.copyfile(source,HERE/target)
print(json.dumps({'status':'PASS','previous_publication':'d425c2942983129a513d44dcaa196a3f44d7b87b'}))
