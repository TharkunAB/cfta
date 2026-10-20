import json,shutil
from pathlib import Path
HERE=Path(__file__).resolve().parent
for source,target in [('/tmp/mcfta-native-original-node-row-origins-fixture','node-fixture'),('/tmp/mcfta-native-original-node-row-origins-fixture-review','fixture-review')]:
 assert not (HERE/target).exists();shutil.copytree(source,HERE/target)
for ext in ['json','log','limits.json','peaks.txt','source.py','usage.json']:
 shutil.copyfile('/tmp/mcfta-node-archive-components.'+ext,HERE/('archive-components-run.'+ext))
print(json.dumps({'status':'PASS','archived_components':2}))
