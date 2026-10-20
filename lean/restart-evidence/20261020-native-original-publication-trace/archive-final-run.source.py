import json,shutil
from pathlib import Path
HERE=Path(__file__).resolve().parent
for source,target in [('/tmp/mcfta-native-original-publication-trace-fixture','trace-fixture'),('/tmp/mcfta-native-original-publication-trace-fixture-review','fixture-review'),('/tmp/mcfta-native-indexed-resumption-next-plan','next-resumption-plan')]:
 assert not (HERE/target).exists()
 shutil.copytree(source,HERE/target)
for ext in ['json','log','limits.json','peaks.txt','source.py','usage.json']:
 shutil.copyfile('/tmp/mcfta-trace-archive-components.'+ext,HERE/('archive-components-run.'+ext))
print(json.dumps({'status':'PASS','archived_components':3}))
