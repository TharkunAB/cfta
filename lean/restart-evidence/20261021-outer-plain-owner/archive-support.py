import json,shutil
from pathlib import Path
H=Path(__file__).resolve().parent
for stem in ['mcfta-outer-owner-verify-1','mcfta-outer-owner-verify-2','mcfta-outer-owner-final-archive-1']:
 for suffix in ['json','log','limits.json','peaks.txt','source.py','usage.json']:
  p=Path('/tmp')/(stem+'.'+suffix);assert p.exists(),p;shutil.copyfile(p,H/'root-support'/p.name)
print(json.dumps({'status':'PASS'}))
