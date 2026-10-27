from pathlib import Path
import hashlib,json,os,subprocess
root=Path('/home/tritlo/Code/mcfta');area=Path('/tmp/mcfta-recursive-driver-arity-20261027')
entries=[('FiniteArityEffects','v1','42e51cdc320ba7247622595e7b87bcc1b952f2c9c62ac6ace6fc9468984908f2'),('FiniteCallbackResourcesArity','v1','cedbab1a1d656da9a641554748695d35b1f1a0113f33adcf142f76055c31a9b9'),('FiniteReceiptResourcesArity','v1','09998c739f4f2e91dcbbaae67166987404938cc0362396b44f4f3a9db1ca35a4'),('FiniteHeadResourcesArity','v1','6da92f73bd7064e9d06b1c63e50dcf7a7ece6dfe8f5614869307db9a387a729f'),('FiniteSiblingResourcesArity','v2-sibling','3492a1f1ba8987211a7c8474188fb987699b143b4d1ae2b37277fd25f58b1ccb'),('FiniteSiblingFinishResourcesArity','v1','3216de96d41fdb4151ba27abf96b90e5da0962f0c03f22846444ab5ec48194c2')]
env=dict(os.environ,XDG_RUNTIME_DIR='/run/user/1000',DBUS_SESSION_BUS_ADDRESS='unix:path=/run/user/1000/bus',HEAVY_PEAKS=str(area/'heavy-peaks'))
for short,version,sha in entries:
 module='SourcePruningEnumeration'+short;relative='callback-head-scan/drafts/'+version+'/'+module+'.lean';src=area/relative
 assert hashlib.sha256(src.read_bytes()).hexdigest()==sha
 slug='strict-'+short.lower()+'-1';command=['/home/tritlo/Code/heavy-management/bin/capped','--mem','4G','--time','5m','python3',str(area/'check-overlay.py'),slug,relative,module]
 r=subprocess.run(command,cwd=root,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT);(area/('driver-'+slug+'.log')).write_bytes(r.stdout);print(module+' exit '+str(r.returncode),flush=True)
 if r.returncode:print(r.stdout.decode());raise SystemExit(r.returncode)
