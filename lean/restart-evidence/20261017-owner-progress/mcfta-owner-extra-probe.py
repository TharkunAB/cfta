import sys,os,json,subprocess,shutil,hashlib,datetime
from pathlib import Path
root=Path('/home/tritlo/Code/mcfta')
evidence=root/'lean/restart-evidence/20261017-owner-progress'
name,source=sys.argv[1:]
frozen=evidence/(name+'.source.lean')
assert not frozen.exists(),str(frozen)
shutil.copyfile(root/source,frozen)
env=dict(os.environ,LEAN_PATH=str(root/'lean/.lake/build/lib/lean'),XDG_RUNTIME_DIR='/run/user/1000',DBUS_SESSION_BUS_ADDRESS='unix:path=/run/user/1000/bus',HEAVY_PEAKS=str(evidence/'supplemental-probe-peaks.txt'),OWNER_SOURCE=str(frozen),OWNER_LIMITS=str(evidence/(name+'.limits.json')))
command=['/home/tritlo/Code/heavy-management/bin/capped','--mem','4G','--time','5m','python3','/tmp/mcfta-owner-capped.py']
with (evidence/(name+'.log')).open('w') as log:
 result=subprocess.run(command,env=env,stdout=log,stderr=subprocess.STDOUT)
report={'command':command,'exit_code':result.returncode,'source':frozen.name,'sha256':hashlib.sha256(frozen.read_bytes()).hexdigest(),'observed_at':datetime.datetime.now(datetime.timezone.utc).isoformat()}
(evidence/(name+'.json')).write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report))
raise SystemExit(result.returncode)
