from pathlib import Path
import hashlib,json,os,subprocess
root=Path('/home/tritlo/Code/mcfta');area=Path('/tmp/mcfta-recursive-worker-arity-20261027')
entries=[
('SelectedEdgeResourcesArity','history-arity-frontier/drafts/v1-selected-captured-head','a1ca32c593aaf9cf80c4bf8f307741fcc241333b2c8e9e914b88ec362d752586','selected-edge-resources-arity'),
('CapturedEdgeResourcesArity','history-arity-frontier/drafts/v1-selected-captured-head','89355592202ed16822927fc1032bb0079ea3524714aff4a09a4c900212cbf8ba','captured-edge-resources-arity'),
('NativeHeadResourcesArity','history-arity-frontier/drafts/v2-head','05912e746878c9ef8dcd74bef66c15b4b1927b1033f2cd4ffbe62ddca9b53ea5','native-head-resources-arity'),
('NativeHeadBoundedResourcesArity','history-arity-frontier/drafts/v1-head-bounded','84885e2b807253e35532859fb4c811d388e446928e28b7bdc2329d5941965767','native-head-bounded-resources-arity')]
env=dict(os.environ,XDG_RUNTIME_DIR='/run/user/1000',DBUS_SESSION_BUS_ADDRESS='unix:path=/run/user/1000/bus',HEAVY_PEAKS=str(area/'heavy-peaks'))
cap=['/home/tritlo/Code/heavy-management/bin/capped','--mem','4G','--time','5m','python3']
for short,folder,sha,slug in entries:
 module='SourcePruningEnumeration'+short;relative=folder+'/'+module+'.lean';src=area/relative
 assert hashlib.sha256(src.read_bytes()).hexdigest()==sha
 command=cap+[str(area/'check-draft.py'),'strict-'+slug+'-1',relative,module]
 result=subprocess.run(command,cwd=root,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 (area/('driver-strict-'+slug+'-1.log')).write_bytes(result.stdout)
 print('strict '+module+' exit '+str(result.returncode),flush=True)
 if result.returncode:
  print(result.stdout.decode());raise SystemExit(result.returncode)
 report=json.loads((area/('strict-'+slug+'-1/report.json')).read_text());assert report['exit_code']==0 and report['bytes']==0
 target=root/'lean/MicroCFTA'/(module+'.lean');assert not target.exists();target.write_bytes(src.read_bytes())
 command=cap+[str(area/'check-installed.py'),'lake','build-'+slug+'-1','MicroCFTA.'+module]
 result=subprocess.run(command,cwd=root,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 (area/('driver-build-'+slug+'-1.log')).write_bytes(result.stdout)
 print('build '+module+' exit '+str(result.returncode),flush=True)
 if result.returncode:
  print(result.stdout.decode());raise SystemExit(result.returncode)
