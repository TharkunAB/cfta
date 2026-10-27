from pathlib import Path
import hashlib,os,subprocess
root=Path('/home/tritlo/Code/mcfta');area=Path('/tmp/mcfta-recursive-driver-arity-20261027')
entries=[('FiniteOrdinaryResourcesArity','ordinary-arity/drafts/v1','0f4aea6c2cf4038f62303f5124a7712e5e9446b20e212e3c04e2ab49e6c47bcc'),('FiniteOrdinaryForecastResourcesArity','ordinary-arity/drafts/v1','6dbc33c769614b2c89222a314a51b05ef6c2ad0d9012b2263070e0a60ea364ff'),('FiniteParkedResourcesArity','driver-step/drafts/v1','3534b9df6884e7253da7db81e0ed8eb15d80c60d95a0e7f28205f18078b38d6f'),('FiniteExpansionResourcesArity','driver-step/drafts/v1','6239cb5165560abb3860474ae4483dc97c40ac75eb1f85e979ee06c813323a0a'),('FiniteRunStepArity','driver-step/drafts/v1','d0f1732cf3dd1cfe2f7a7a408a4515f5d40c4cb11b41b4e5fa4fdcea0f443efe'),('FiniteResourcesArity','driver-step/drafts/v1','242be4a38fad5886e0e9c485a1982fba01f5a8bdfc750d39b3f52a3c68bc131c')]
env=dict(os.environ,XDG_RUNTIME_DIR='/run/user/1000',DBUS_SESSION_BUS_ADDRESS='unix:path=/run/user/1000/bus',HEAVY_PEAKS=str(area/'heavy-peaks'))
for short,folder,sha in entries:
 module='SourcePruningEnumeration'+short;relative=folder+'/'+module+'.lean';assert hashlib.sha256((area/relative).read_bytes()).hexdigest()==sha
 slug='strict-'+short.lower()+'-1';command=['/home/tritlo/Code/heavy-management/bin/capped','--mem','4G','--time','5m','python3',str(area/'check-overlay.py'),slug,relative,module]
 r=subprocess.run(command,cwd=root,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT);(area/('driver-'+slug+'.log')).write_bytes(r.stdout);print(module+' exit '+str(r.returncode),flush=True)
 if r.returncode:print(r.stdout.decode());raise SystemExit(r.returncode)
