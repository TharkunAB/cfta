import datetime, hashlib, json, os, subprocess, sys
from pathlib import Path
root=Path('/home/tritlo/Code/mcfta')
here=Path(__file__).resolve().parent
name,kind,sourceName,*options=sys.argv[1:]
assert not (here/(name+'.json')).exists()
usage=json.loads(subprocess.check_output(['python3','/tmp/mcfta-weekly-usage.py'],text=True))
(here/(name+'.usage.json')).write_text(json.dumps(usage,indent=2)+'\n')
assert usage['age_seconds']<120 and usage['remaining_percent']>1,usage
source=Path(sourceName)
outputs=[]
if kind=='source':
 frozen=here/(name+'.source.lean')
 command=['/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean','-Dlinter.all=true',str(frozen)]
elif kind=='canonical':
 frozen=here/(name+'.inputs/MicroCFTA/SourceCurrentNativeRequestPositivePositions.lean')
 output=here/'import-tree/MicroCFTA/SourceCurrentNativeRequestPositivePositions.olean'
 assert not output.exists()
 output.parent.mkdir(parents=True,exist_ok=True)
 command=['/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean','-Dlinter.all=true','-R',str(here/(name+'.inputs')),'-o',str(output),str(frozen)]
 outputs=[output]
else:
 raise AssertionError(kind)
assert not frozen.exists()
frozen.parent.mkdir(parents=True,exist_ok=True)
frozen.write_bytes(source.read_bytes())
wrapped=['/home/tritlo/Code/heavy-management/bin/capped','--mem','4G','--time','5m','python3',str(here/'query-stores-capped-worker.py')]
library=options[0] if options else str(root/'lean/.lake/build/lib/lean')
env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1',LEAN_PATH=library,XDG_RUNTIME_DIR='/run/user/1000',DBUS_SESSION_BUS_ADDRESS='unix:path=/run/user/1000/bus',HEAVY_PEAKS=str(here/'query-stores-peaks.txt'),QUERY_STORES_LIMITS=str(here/(name+'.limits.json')),QUERY_STORES_COMMAND=json.dumps(command))
started=datetime.datetime.now(datetime.timezone.utc).isoformat()
with (here/(name+'.log')).open('xb') as log:
 result=subprocess.run(wrapped,cwd=root/'lean',env=env,stdout=log,stderr=subprocess.STDOUT)
report=dict(command=command,wrapper=wrapped,exit_code=result.returncode,started_at=started,observed_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),source=str(frozen.relative_to(here)),sha256=hashlib.sha256(frozen.read_bytes()).hexdigest(),log=name+'.log',limits=name+'.limits.json',lean_path=library,outputs=[dict(path=str(p.relative_to(here)),bytes=p.stat().st_size,sha256=hashlib.sha256(p.read_bytes()).hexdigest()) for p in outputs if p.exists()])
(here/(name+'.json')).write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report))
if result.returncode: print((here/(name+'.log')).read_text()[-22000:])
raise SystemExit(result.returncode)
