import datetime, hashlib, json, os, subprocess
from pathlib import Path
root=Path('/home/tritlo/Code/mcfta')
here=Path(__file__).resolve().parent
name='upstream-review-binders-5'
assert not (here/(name+'.json')).exists()
command=['/home/tritlo/.nix-profile/bin/nix-shell','--option','substituters','','--option','builders','','--option','max-jobs','0',str(root/'shell.nix'),'--run','bash /tmp/mcfta-upstream-binders-20261020/run-5.sh']
wrapped=['/home/tritlo/Code/heavy-management/bin/capped','--mem','4G','--time','5m','python3',str(here/'upstream-review-capped-worker.py')]
env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1',XDG_RUNTIME_DIR='/run/user/1000',DBUS_SESSION_BUS_ADDRESS='unix:path=/run/user/1000/bus',HEAVY_PEAKS=str(here/'upstream-review-peaks.txt'),UPSTREAM_REVIEW_LIMITS=str(here/(name+'.limits.json')),UPSTREAM_REVIEW_COMMAND=json.dumps(command))
started=datetime.datetime.now(datetime.timezone.utc).isoformat()
with (here/(name+'.log')).open('xb') as log:
 result=subprocess.run(wrapped,env=env,cwd=root,stdout=log,stderr=subprocess.STDOUT)
report=dict(command=command,wrapper=wrapped,exit_code=result.returncode,started_at=started,observed_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),log=name+'.log',limits=name+'.limits.json',source='upstream-review-binders-repro.hs',source_sha256=hashlib.sha256((here/'upstream-review-binders-repro.hs').read_bytes()).hexdigest())
(here/(name+'.json')).write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report))
print((here/(name+'.log')).read_text()[-12000:])
raise SystemExit(result.returncode)
