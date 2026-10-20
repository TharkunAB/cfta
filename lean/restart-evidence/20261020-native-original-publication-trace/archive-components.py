import json,shutil,subprocess
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
for source,target in [('/tmp/mcfta-native-original-publication-trace','trace-module'),('/tmp/mcfta-native-publication-order-helpers','order-helpers'),('/tmp/mcfta-native-original-publication-trace-math-review','source-review')]:
 assert not (HERE/target).exists()
 shutil.copytree(source,HERE/target)
for stem,label in [('mcfta-trace-bootstrap','bootstrap-run'),('mcfta-trace-format-check','format-check'),('mcfta-binders-docs-closure-1','previous-closure')]:
 for ext in ['json','log','limits.json','peaks.txt','source.py','usage.json']:
  shutil.copyfile('/tmp/'+stem+'.'+ext,HERE/(label+'.'+ext))
for source,target in [('/tmp/mcfta-binders-docs-publication.json','previous-publication.json'),('/tmp/mcfta-binders-docs-board-readback.json','previous-board-readback.json')]:
 shutil.copyfile(source,HERE/target)
proof=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip()
assert proof=='def05b051f229383856dd88fecc29c0a14743fd3'
(HERE/'proof-commit.txt').write_text(proof+'\n')
print(json.dumps({'status':'PASS','archived_components':3,'proof':proof}))
