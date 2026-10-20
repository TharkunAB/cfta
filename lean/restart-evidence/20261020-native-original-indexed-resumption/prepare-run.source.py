import runpy,shutil
from pathlib import Path
HERE=Path(__file__).resolve().parent
for ext in ['json','log','limits.json','peaks.txt','source.py','usage.json']:
 shutil.copyfile('/tmp/mcfta-indexed-archive-final.'+ext,HERE/('archive-final-run.'+ext))
runpy.run_path(str(HERE/'prepare-metadata.py'))
runpy.run_path(str(HERE/'write-current-documents.py'))
