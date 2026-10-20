import json,shutil
from pathlib import Path
here=Path('/home/tritlo/Code/mcfta/lean/restart-evidence/20261020-native-original-captured-node-rows')
for source,target in [('/tmp/mcfta-native-original-captured-node-rows','capture-module'),('/tmp/mcfta-native-captured-unfold-node-core','unfold-core'),('/tmp/mcfta-native-original-captured-node-rows-math-review','source-review')]:
    assert not (here/target).exists()
    shutil.copytree(source,here/target)
for ext in ['json','log','limits.json','peaks.txt','source.py','usage.json']:
    shutil.copyfile('/tmp/mcfta-captured-archive-previous-1.'+ext,here/('archive-previous-run.'+ext))
(here/'proof-commit.txt').write_text('de1791f450e99f036ce0e29ef4bcb5b7c16b12fb\n')
print(json.dumps({'status':'PASS','archived_components':3,'proof':'de1791f450e99f036ce0e29ef4bcb5b7c16b12fb'}))
