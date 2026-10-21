import datetime, hashlib, json, os, subprocess, sys
from pathlib import Path
root=Path('/home/tritlo/Code/mcfta')
here=Path(__file__).resolve().parent
name,source_name,*options=sys.argv[1:]
canonical=options==['--canonical']
assert not options or canonical
assert not (here/(name+'.json')).exists()
usage=json.loads(subprocess.check_output(['python3','/tmp/mcfta-weekly-usage.py'],text=True))
(here/(name+'.usage.json')).write_text(json.dumps(usage,indent=2)+'\n')
assert usage['age_seconds']<120 and usage['remaining_percent']>1,usage
source=here/source_name
frozen=(here/(name+'-input')/'MicroCFTA'/source.name) if canonical else here/(name+'.source.lean')
frozen.parent.mkdir(parents=True,exist_ok=True)
assert not frozen.exists()
frozen.write_bytes(source.read_bytes())
command=['/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean','-Dlinter.all=true']
output=None
if canonical:
 output=here/'import-tree'/'MicroCFTA'/(source.stem+'.olean')
 output.parent.mkdir(parents=True,exist_ok=True)
 command += ['-R',str(here/(name+'-input')),'-o',str(output)]
command += [str(frozen)]
wrapped=['/home/tritlo/Code/heavy-management/bin/capped','--mem','4G','--time','5m','python3',str(here/'raw-projection-capped-worker.py')]
env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1',LEAN_PATH='/tmp/mcfta-raw-corridor-projection-imports:'+str(root/'lean/.lake/build/lib/lean'),XDG_RUNTIME_DIR='/run/user/1000',DBUS_SESSION_BUS_ADDRESS='unix:path=/run/user/1000/bus',HEAVY_PEAKS=str(here/'raw-projection-peaks.txt'),RAW_PROJECTION_LIMITS=str(here/(name+'.limits.json')),RAW_PROJECTION_COMMAND=json.dumps(command))
started=datetime.datetime.now(datetime.timezone.utc).isoformat()
with (here/(name+'.log')).open('xb') as log:
 result=subprocess.run(wrapped,cwd=root/'lean',env=env,stdout=log,stderr=subprocess.STDOUT)
report=dict(command=command,wrapper=wrapped,exit_code=result.returncode,started_at=started,observed_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),kind='canonical' if canonical else 'source',lean_path=env['LEAN_PATH'],source=str(frozen.relative_to(here)),output=str(output.relative_to(here)) if output else None,sha256=hashlib.sha256(frozen.read_bytes()).hexdigest(),log=name+'.log',limits=name+'.limits.json')
(here/(name+'.json')).write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report))
if result.returncode: print((here/(name+'.log')).read_text()[-22000:])
raise SystemExit(result.returncode)
