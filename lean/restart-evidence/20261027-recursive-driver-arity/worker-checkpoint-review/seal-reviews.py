from pathlib import Path
import json,hashlib,subprocess
A=Path('/tmp/mcfta-recursive-driver-arity-20261027');R=Path('/home/tritlo/Code/mcfta')
def sha(b):return hashlib.sha256(b).hexdigest()
names=['callback-head-scan-independent-review','driver-step-independent-review','history-render-independent-review','worker-checkpoint-review']
# Validate every retained source identity and literal cut before any seal is written.
for name in names:
 D=A/name;assert not (D/'FROZEN.json').exists(),name
 for x in json.loads((D/'source-pins-final.json').read_text())['sources']:
  b=(D/x['copy']).read_bytes();assert len(b)==x['bytes'] and sha(b)==x['sha256'],(name,x['copy'])
  source=Path(x['source_path'])
  if x.get('historical_metadata'):
   old=json.loads(b);current=json.loads(source.read_bytes());assert {k:v for k,v in current.items() if k!='v3_actual_inverse_checked'}==old and current['v3_actual_inverse_checked'] is True
  else:assert source.read_bytes()==b,(name,str(source))
  for c in x.get('cuts',[]):
   cut=(D/c['path']).read_bytes();assert cut==b''.join(b.splitlines(keepends=True)[c['start_line']-1:c['end_line']]),(name,c['path'])
   assert len(cut)==c['bytes'] and sha(cut)==c['sha256']
for x in json.loads((A/'document-validation.json').read_text()):
 b=(R/x['path']).read_bytes();assert len(b)==x['bytes'] and sha(b)==x['sha256']
 if 'offset' in x:assert b[:x['offset']]+b[x['offset']+x['inserted_bytes']:]==(A/'prior-documents'/x['path']).read_bytes()
for module,cn in json.loads((A/'strict-checks.json').read_text()).items():
 report=json.loads((A/cn/'report.json').read_text());assert report['exit_code']==0
 for field in ('memory.max','memory.high'):assert report['cgroup_limits'][field]=='4294967296'
 assert report['cgroup_limits']['memory.swap.max']=='0'
stamp=subprocess.check_output(['date','+%Y-%m-%d %H:%M:%S %Z'],text=True).strip()
result=[]
for name in names:
 D=A/name;files=sorted((p for p in D.rglob('*') if p.is_file() and p.relative_to(D).as_posix() not in ('pins.json','FROZEN.json')),key=lambda p:p.relative_to(D).as_posix());payloads=[]
 for p in files:
  b=p.read_bytes();payloads.append({'path':p.relative_to(D).as_posix(),'bytes':len(b),'sha256':sha(b)})
 pins={'payloads':payloads};pb=(json.dumps(pins,indent=2)+'\n').encode();(D/'pins.json').write_bytes(pb)
 frozen={'status':'FROZEN','source_head':'074e4aaabdc8a3cd2d1bdf8722e268460c178dc7','sealed_at':stamp,'pins_sha256':sha(pb),'payload_count':len(payloads),'exact_file_count':len(payloads)+2,'review':'CLEAR; bounded independent source/public/document review. No compiler, builds, Git, network, board or repository edits by reviewer.'};fb=(json.dumps(frozen,indent=2)+'\n').encode();(D/'FROZEN.json').write_bytes(fb)
 assert len([p for p in D.rglob('*') if p.is_file()])==frozen['exact_file_count']
 for x in payloads:
  b=(D/x['path']).read_bytes();assert len(b)==x['bytes'] and sha(b)==x['sha256']
 assert sha((D/'pins.json').read_bytes())==frozen['pins_sha256']
 result.append({'bundle':name,'payload_count':len(payloads),'exact_file_count':len(payloads)+2,'pins_sha256':sha(pb),'FROZEN_sha256':sha(fb)})
print(json.dumps({'status':'SEALED; all intended files present; all writes stopped','sealed_at':stamp,'bundles':result},indent=2))
