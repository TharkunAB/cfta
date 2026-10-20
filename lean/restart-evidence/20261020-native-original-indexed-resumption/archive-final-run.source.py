import json,shutil
from pathlib import Path
HERE=Path(__file__).resolve().parent
for source,target in [('/tmp/mcfta-native-original-indexed-resumption-fixture','indexed-fixture'),('/tmp/mcfta-native-original-indexed-resumption-fixture-review','fixture-review'),('/tmp/mcfta-native-node-ancestry-next-plan','next-node-plan')]:
 assert not (HERE/target).exists();shutil.copytree(source,HERE/target)
for ext in ['json','log','limits.json','peaks.txt','source.py','usage.json']:
 shutil.copyfile('/tmp/mcfta-indexed-archive-components.'+ext,HERE/('archive-components-run.'+ext))
print(json.dumps({'status':'PASS','archived_components':3}))
