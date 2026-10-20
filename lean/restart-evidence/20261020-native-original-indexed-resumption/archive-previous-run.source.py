import json,shutil
from pathlib import Path
HERE=Path(__file__).resolve().parent
for stem,label in [('mcfta-indexed-bootstrap','bootstrap-run'),('mcfta-trace-finalize-1','previous-finalize'),('mcfta-trace-publish-1','previous-publish'),('mcfta-trace-closure-1','previous-closure')]:
 for ext in ['json','log','limits.json','peaks.txt','source.py','usage.json']:
  shutil.copyfile('/tmp/'+stem+'.'+ext,HERE/(label+'.'+ext))
for source,target in [('/tmp/mcfta-native-trace-publication.json','previous-publication.json'),('/tmp/mcfta-native-trace-board-readback.json','previous-board-readback.json'),('/tmp/mcfta-native-trace-push.log','previous-push.log'),('/tmp/mcfta-native-trace-remote.txt','previous-remote.txt')]:
 shutil.copyfile(source,HERE/target)
print(json.dumps({'status':'PASS','previous_publication':'1c613eabeee9dc36961f9710bd644f89212a8b76'}))
