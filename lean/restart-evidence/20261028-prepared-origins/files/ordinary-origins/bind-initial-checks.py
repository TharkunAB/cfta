from pathlib import Path
import hashlib,json,shutil
base=Path('/tmp/mcfta-prepared-origins-20261028')
out=base/'ordinary-origins'
records=[]
for name in ['traversal-v1','selected-v1','traversal-build']:
 src=base/name; dest=out/'checks'/name
 for p in sorted(src.rglob('*')):
  if p.is_file():
   d=dest/p.relative_to(src); d.parent.mkdir(parents=True,exist_ok=True); shutil.copyfile(p,d)
 report=json.loads((dest/'report.json').read_text()); raw=(dest/'raw.log').read_bytes()
 assert report['exit_code']==0 and report['bytes']==len(raw) and report['sha256']==hashlib.sha256(raw).hexdigest()
 assert report['cgroup_limits']=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
 if 'source_sha256' in report:
  snapshot=next((dest/'MicroCFTA').glob('*.lean'))
  assert hashlib.sha256(snapshot.read_bytes()).hexdigest()==report['source_sha256']
 records.append({'attempt':name,'report':str((dest/'report.json').relative_to(out)),'exit_code':0,'raw_bytes':len(raw),'raw_sha256':hashlib.sha256(raw).hexdigest(),'scope':'Owner candidate strict source check' if name!='traversal-build' else 'Installed traversal module Lake build; one replayed unchanged older warning'})
(out/'checked-status-v1.json').write_text(json.dumps({'status':'PASS for both exact unmodified v1 owner candidates; overall review OPEN','checks':records},indent=2)+'\n')
