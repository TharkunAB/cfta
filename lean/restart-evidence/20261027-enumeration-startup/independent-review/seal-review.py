from pathlib import Path
import json,hashlib,subprocess
D=Path('/tmp/mcfta-enumeration-startup-20261027/independent-review')
def sha(b):return hashlib.sha256(b).hexdigest()
assert not (D/'FROZEN.json').exists()
for x in json.loads((D/'source-pins-final.json').read_text())['sources']:
 b=(D/x['copy']).read_bytes();assert len(b)==x['bytes'] and sha(b)==x['sha256'];assert Path(x['source_path']).read_bytes()==b,x['source_path']
 for c in x.get('cuts',[]):
  cb=(D/c['path']).read_bytes();assert 1<=c['start_line']<=c['end_line']<=len(b.splitlines());assert cb==b''.join(b.splitlines(keepends=True)[c['start_line']-1:c['end_line']]);assert len(cb)==c['bytes'] and sha(cb)==c['sha256']
paths=sorted([p for p in D.rglob('*') if p.is_file() and p.relative_to(D).as_posix() not in ('pins.json','FROZEN.json')],key=lambda p:p.relative_to(D).as_posix())
payloads=[]
for p in paths:
 b=p.read_bytes();payloads.append({'path':p.relative_to(D).as_posix(),'bytes':len(b),'sha256':sha(b)})
pb=(json.dumps({'payloads':payloads},indent=2)+'\n').encode();(D/'pins.json').write_bytes(pb)
stamp=subprocess.check_output(['date','+%Y-%m-%d %H:%M:%S %Z'],text=True).strip()
f={'status':'FROZEN','source_head':'63942a2bff4143e44fdc16ea026df24c0ac9d6b8','sealed_at':stamp,'pins_sha256':sha(pb),'payload_count':len(payloads),'exact_file_count':len(payloads)+2,'review':'CLEAR; bounded two-module source/public/document review; all intended files present; all writes stopped'}
fb=(json.dumps(f,indent=2)+'\n').encode();(D/'FROZEN.json').write_bytes(fb)
assert len([p for p in D.rglob('*') if p.is_file()])==f['exact_file_count']
for x in payloads:
 b=(D/x['path']).read_bytes();assert len(b)==x['bytes'] and sha(b)==x['sha256']
assert sha((D/'pins.json').read_bytes())==f['pins_sha256']
print(json.dumps({**f,'FROZEN_sha256':sha(fb)},indent=2))
