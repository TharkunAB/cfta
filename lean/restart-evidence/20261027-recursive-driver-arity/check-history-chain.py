from pathlib import Path
import hashlib,os,subprocess
root=Path('/home/tritlo/Code/mcfta');area=Path('/tmp/mcfta-recursive-driver-arity-20261027')
entries=[('HistoryOutputArity','history-output-arity/drafts/v1','fbb0698a0f658b49f83722523e70dcd9da22bf43266daf561878b3c52129ce3d'),('FiniteHistoryResourcesArity','history-output-arity/drafts/v1','544fc38434ae9e24d63cd8543bf01e68280d986160e7cb9395416d3f665f16bb'),('FiniteHistoryRenderingArity','render-consumer/drafts/v1','b54354c0c3e28a27b456adac0d2ed7d9e9fd3ea03a2bd359c4168e3ae7e9159d')]
env=dict(os.environ,XDG_RUNTIME_DIR='/run/user/1000',DBUS_SESSION_BUS_ADDRESS='unix:path=/run/user/1000/bus',HEAVY_PEAKS=str(area/'heavy-peaks'))
for short,folder,sha in entries:
 module='SourcePruningEnumeration'+short;relative=folder+'/'+module+'.lean';assert hashlib.sha256((area/relative).read_bytes()).hexdigest()==sha
 slug='strict-'+short.lower()+'-1';command=['/home/tritlo/Code/heavy-management/bin/capped','--mem','4G','--time','5m','python3',str(area/'check-overlay.py'),slug,relative,module]
 r=subprocess.run(command,cwd=root,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT);(area/('driver-'+slug+'.log')).write_bytes(r.stdout);print(module+' exit '+str(r.returncode),flush=True)
 if r.returncode:print(r.stdout.decode());raise SystemExit(r.returncode)
