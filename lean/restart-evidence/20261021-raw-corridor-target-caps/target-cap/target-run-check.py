import datetime,hashlib,json,os,subprocess,sys
from pathlib import Path

H=Path(__file__).resolve().parent
R=Path('/home/tritlo/Code/mcfta')
stem,source_name,library,*mode=sys.argv[1:]
assert not (H/(stem+'.json')).exists()
usage=json.loads(subprocess.check_output(['python3','/tmp/mcfta-weekly-usage.py'],text=True))
(H/(stem+'.usage.json')).write_text(json.dumps(usage,indent=2)+'\n')
assert usage['age_seconds']<120 and usage['remaining_percent']>1
source=H/source_name
frozen=H/(stem+'.source.lean')
frozen.write_bytes(source.read_bytes())
command=['/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean','-Dlinter.all=true']
if mode:
    assert mode==['canonical']
    inputs=H/(stem+'.input')
    actual=inputs/'MicroCFTA'/source.name
    actual.parent.mkdir(parents=True)
    actual.write_bytes(source.read_bytes())
    command+=['-R',str(inputs),'-o',str(Path(library)/'MicroCFTA'/source.with_suffix('.olean').name),str(actual)]
else:
    command.append(str(frozen))
wrapper=['/home/tritlo/Code/heavy-management/bin/capped','--mem','4G','--time','5m','python3',str(H/'target-capped-worker.py')]
env={**os.environ,'PYTHONDONTWRITEBYTECODE':'1','LEAN_PATH':library,'XDG_RUNTIME_DIR':'/run/user/1000','DBUS_SESSION_BUS_ADDRESS':'unix:path=/run/user/1000/bus','HEAVY_PEAKS':str(H/'target-peaks.txt'),'SHARED_CAP_LIMITS':str(H/(stem+'.limits.json')),'SHARED_CAP_COMMAND':json.dumps(command)}
with (H/(stem+'.log')).open('xb') as log:
    result=subprocess.run(wrapper,cwd=R/'lean',env=env,stdout=log,stderr=subprocess.STDOUT)
receipt={'command':command,'wrapper':wrapper,'exit_code':result.returncode,'observed_at':datetime.datetime.now(datetime.timezone.utc).isoformat(),'source':frozen.name,'sha256':hashlib.sha256(frozen.read_bytes()).hexdigest(),'lean_path':library,'log':stem+'.log','limits':stem+'.limits.json'}
(H/(stem+'.json')).write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt))
if result.returncode: print((H/(stem+'.log')).read_text()[-24000:])
raise SystemExit(result.returncode)
