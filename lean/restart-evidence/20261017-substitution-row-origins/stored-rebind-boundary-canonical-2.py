from pathlib import Path
import datetime,hashlib,json,os,subprocess
ROOT=Path('/home/tritlo/Code/mcfta');HERE=Path(__file__).resolve().parent
source=ROOT/'lean/MicroCFTA/SourceCurrentStoredRebindBoundary.lean'
command=['/home/tritlo/Code/heavy-management/bin/capped','--mem','4G','--time','5m','bash',str(HERE/'stored-rebind-boundary-canonical-2.sh')]
env=os.environ.copy();env.update(HEAVY_PEAKS=str(HERE/'stored-rebind-boundary-peaks.txt'),XDG_RUNTIME_DIR='/run/user/1000',DBUS_SESSION_BUS_ADDRESS='unix:path=/run/user/1000/bus')
with (HERE/'stored-rebind-boundary-canonical-2.log').open('xb') as output:
 result=subprocess.run(command,cwd=ROOT,env=env,stdout=output,stderr=subprocess.STDOUT)
assert source.read_bytes()==(HERE/'stored-rebind-boundary-canonical-2.source.lean').read_bytes()
(HERE/'stored-rebind-boundary-canonical-2.json').write_text(json.dumps(dict(command=command,exit_code=result.returncode,source='lean/MicroCFTA/SourceCurrentStoredRebindBoundary.lean',source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),timestamp=datetime.datetime.now().astimezone().isoformat()),indent=2)+'\n')
print('canonical exit',result.returncode);print((HERE/'stored-rebind-boundary-canonical-2.log').read_text()[-3000:]);raise SystemExit(result.returncode)
