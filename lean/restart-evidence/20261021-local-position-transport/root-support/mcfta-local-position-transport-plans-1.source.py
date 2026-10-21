import json,shutil,subprocess
from pathlib import Path
H=Path(__file__).resolve().parent;R=H.parents[2]
items=[]
for source,destination in [('mcfta-maybe-mu-input-position-investigation','maybe-mu-plan'),('mcfta-maybe-mu-positional-premise-review','maybe-mu-premise-review'),('mcfta-target-operand-position-investigation','target-plan')]:
 d=H/destination;assert not d.exists();shutil.copytree('/tmp/'+source,d)
 for mode in [[],['--live']]:subprocess.run(['/usr/bin/python3',str(d/'verify.py'),'--root',str(R),*mode],cwd='/',check=True,stdout=subprocess.DEVNULL)
 items.append({'path':destination,'verifier':'verify.py','extra':['--root',str(R)],'live':True})
(H/'plan-components.json').write_text(json.dumps(items,indent=2)+'\n')
print(json.dumps({'status':'PASS','zero_job_plan_components':len(items),'new_lean_jobs':0}))
