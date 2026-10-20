import json,shutil,subprocess
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
for source,target in [('/tmp/mcfta-native-original-node-row-origins','node-module'),('/tmp/mcfta-native-original-node-row-origins-math-review','source-review')]:
 assert not (HERE/target).exists();shutil.copytree(source,HERE/target)
for ext in ['json','log','limits.json','peaks.txt','source.py','usage.json']:
 shutil.copyfile('/tmp/mcfta-node-archive-previous.'+ext,HERE/('archive-previous-run.'+ext))
proof=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip();assert proof=='6489bddee3161ef38e2d74008f8877cc00fdcde9';(HERE/'proof-commit.txt').write_text(proof+'\n')
print(json.dumps({'status':'PASS','archived_components':2,'proof':proof}))
