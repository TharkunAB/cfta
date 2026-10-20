import json,shutil
from pathlib import Path
here=Path('/home/tritlo/Code/mcfta/lean/restart-evidence/20261020-native-original-captured-node-rows')
for source,target in [('/tmp/mcfta-native-original-captured-node-rows-fixture','capture-fixture'),('/tmp/mcfta-native-original-captured-node-rows-fixture-review','fixture-review')]:
    assert not (here/target).exists()
    shutil.copytree(source,here/target)
for ext in ['json','log','limits.json','peaks.txt','source.py','usage.json']:
    shutil.copyfile('/tmp/mcfta-captured-archive-components-1.'+ext,here/('archive-components-run.'+ext))
print(json.dumps({'status':'PASS','archived_components':2}))
