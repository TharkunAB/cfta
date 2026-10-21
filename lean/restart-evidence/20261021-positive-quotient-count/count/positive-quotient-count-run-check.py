import datetime, hashlib, json, os, subprocess, sys
from pathlib import Path
root=Path('/home/tritlo/Code/mcfta')
here=Path(__file__).resolve().parent
name,kind,*args=sys.argv[1:]
assert not (here/(name+'.json')).exists()
usage=json.loads(subprocess.check_output(['python3',str(here/'positive-quotient-count-weekly-usage.py')],text=True))
(here/(name+'.usage.json')).write_text(json.dumps(usage,indent=2)+'\n')
assert usage['age_seconds']<=600 and usage['remaining_percent']>1,usage
frozen=None
if kind=='source':
 source=Path(args[0])
 frozen=here/(name+'.source.lean')
 assert not frozen.exists()
 frozen.write_bytes(source.read_bytes())
 command=['/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean','-Dlinter.all=true',str(frozen)]
else:
 assert kind=='lake'
 command=['/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake','-d',str(root/'lean'),'build',*args]
wrapped=['/home/tritlo/Code/heavy-management/bin/capped','--mem','4G','--time','5m','python3',str(here/'positive-quotient-count-capped-worker.py')]
env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1',LEAN_PATH=str(root/'lean/.lake/build/lib/lean'),XDG_RUNTIME_DIR='/run/user/1000',DBUS_SESSION_BUS_ADDRESS='unix:path=/run/user/1000/bus',HEAVY_PEAKS=str(here/'positive-quotient-count-peaks.txt'),QUOTIENT_COUNT_LIMITS=str(here/(name+'.limits.json')),QUOTIENT_COUNT_COMMAND=json.dumps(command))
started=datetime.datetime.now(datetime.timezone.utc).isoformat()
with (here/(name+'.log')).open('xb') as log:
 result=subprocess.run(wrapped,cwd=root/'lean',env=env,stdout=log,stderr=subprocess.STDOUT)
report=dict(command=command,wrapper=wrapped,exit_code=result.returncode,started_at=started,observed_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),source=frozen.name if frozen else None,sha256=hashlib.sha256(frozen.read_bytes()).hexdigest() if frozen else None,log=name+'.log',limits=name+'.limits.json')
(here/(name+'.json')).write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report))
if result.returncode: print((here/(name+'.log')).read_text()[-22000:])
raise SystemExit(result.returncode)
