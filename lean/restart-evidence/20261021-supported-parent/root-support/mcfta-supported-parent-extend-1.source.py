import json,shutil,subprocess
from pathlib import Path
H=Path(__file__).resolve().parent;R=H.parents[2]
d=H/'native-design';assert not d.exists();shutil.copytree('/tmp/mcfta-nested-publication-position-design',d)
for mode in [[],['--live']]:subprocess.run(['/usr/bin/python3',str(d/'verify.py'),'--root',str(R),*mode],cwd='/',check=True,stdout=subprocess.DEVNULL)
p=H/'components.json';items=json.loads(p.read_text());items.append({'path':'native-design','verifier':'verify.py','extra':['--root',str(R)],'live':True});p.write_text(json.dumps(items,indent=2)+'\n')
print(json.dumps({'status':'PASS','components':len(items),'new_lean_jobs':0}))
