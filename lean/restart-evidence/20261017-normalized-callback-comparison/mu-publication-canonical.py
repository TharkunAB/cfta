from pathlib import Path
import datetime, hashlib, json, os, subprocess
HERE=Path(__file__).resolve().parent
ROOT=Path('/home/tritlo/Code/mcfta')
source=ROOT/'lean/MicroCFTA/SourceCurrentNativeMuPublication.lean'
stem='mu-publication-canonical-1'
snapshot=HERE/(stem+'.source.lean')
assert not snapshot.exists()
snapshot.write_bytes(source.read_bytes())
command=['/home/tritlo/Code/heavy-management/bin/capped','--mem','4G','--time','10m','bash',str(HERE/'mu-publication-canonical-worker.sh')]
env=os.environ.copy()
env.update(MU_PUBLICATION_CAPS=str(HERE/(stem+'.caps')),HEAVY_PEAKS=str(HERE/'mu-publication-peaks.txt'),XDG_RUNTIME_DIR='/run/user/1000',DBUS_SESSION_BUS_ADDRESS='unix:path=/run/user/1000/bus')
with (HERE/(stem+'.log')).open('xb') as f:
 result=subprocess.run(command,cwd=ROOT,env=env,stdout=f,stderr=subprocess.STDOUT)
assert snapshot.read_bytes()==source.read_bytes()
(HERE/(stem+'.json')).write_text(json.dumps(dict(command=command,exit_code=result.returncode,source=str(source.relative_to(ROOT)),source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),snapshot=snapshot.name,timestamp=datetime.datetime.now().astimezone().isoformat()),indent=2)+'\n')
print('canonical exit',result.returncode)
print((HERE/(stem+'.log')).read_text()[-3000:])
raise SystemExit(result.returncode)
