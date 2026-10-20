import runpy,shutil
from pathlib import Path
HERE=Path(__file__).resolve().parent
for ext in ['json','log','limits.json','peaks.txt','source.py','usage.json']:
    shutil.copyfile('/tmp/mcfta-captured-archive-plan-1.'+ext,HERE/('archive-plan-run.'+ext))
runpy.run_path(str(HERE/'finalize.py'))
