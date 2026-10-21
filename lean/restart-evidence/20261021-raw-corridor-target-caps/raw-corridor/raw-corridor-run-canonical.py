import datetime, hashlib, json, os, subprocess, sys
from pathlib import Path
root=Path('/home/tritlo/Code/mcfta')
here=Path(__file__).resolve().parent
name,kind,*args=sys.argv[1:]
assert not (here/(name+'.json')).exists()
usage=json.loads(subprocess.check_output(['python3','/tmp/mcfta-weekly-usage.py'],text=True))
(here/(name+'.usage.json')).write_text(json.dumps(usage,indent=2)+'\n')
assert usage['age_seconds']<120 and usage['remaining_percent']>1,usage
assert kind=='canonical'
source=Path(args[0])
input_root=here/(name+'.inputs')
frozen=input_root/'MicroCFTA'/source.name
assert not frozen.exists()
frozen.parent.mkdir(parents=True)
frozen.write_bytes(source.read_bytes())
output=here/'import-tree'/'MicroCFTA'/(source.stem+'.olean')
assert not output.exists()
output.parent.mkdir(parents=True,exist_ok=True)
command=['/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean','-Dlinter.all=true','-R',str(input_root),'-o',str(output),str(frozen)]
wrapped=['/home/tritlo/Code/heavy-management/bin/capped','--mem','4G','--time','5m','python3',str(here/'raw-corridor-capped-worker.py')]
env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1',LEAN_PATH=str(root/'lean/.lake/build/lib/lean'),XDG_RUNTIME_DIR='/run/user/1000',DBUS_SESSION_BUS_ADDRESS='unix:path=/run/user/1000/bus',HEAVY_PEAKS=str(here/'raw-corridor-peaks.txt'),RAW_CORRIDOR_LIMITS=str(here/(name+'.limits.json')),RAW_CORRIDOR_COMMAND=json.dumps(command))
started=datetime.datetime.now(datetime.timezone.utc).isoformat()
with (here/(name+'.log')).open('xb') as log:
 result=subprocess.run(wrapped,cwd=root/'lean',env=env,stdout=log,stderr=subprocess.STDOUT)
report=dict(command=command,wrapper=wrapped,exit_code=result.returncode,started_at=started,observed_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),source=str(frozen.relative_to(here)) if frozen else None,sha256=hashlib.sha256(frozen.read_bytes()).hexdigest() if frozen else None,log=name+'.log',limits=name+'.limits.json')
(here/(name+'.json')).write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report))
if result.returncode: print((here/(name+'.log')).read_text()[-22000:])
raise SystemExit(result.returncode)
