from pathlib import Path
import hashlib,json,datetime
O=Path('/tmp/mcfta-prepared-models-20261028/ordinary-head-models')
assert not (O/'pins.json').exists() and not (O/'FROZEN.json').exists()
def h(b):return hashlib.sha256(b).hexdigest()
rows=[]
for p in sorted(O.rglob('*')):
 assert not p.is_symlink(),p
 if p.is_file():
  assert p.name not in ['pins.json','FROZEN.json'],p
  b=p.read_bytes();rows.append({'path':str(p.relative_to(O)),'bytes':len(b),'sha256':h(b)})
b=(json.dumps({'payloads':rows},indent=2)+'\n').encode()
seal={'status':'FROZEN','sealed_at':datetime.datetime.now().astimezone().isoformat(),'pins_file':'pins.json','pins_bytes':len(b),'pins_sha256':h(b),'payload_count':len(rows),'exact_file_count':len(rows)+2}
(O/'pins.json').write_bytes(b)
(O/'FROZEN.json').write_text(json.dumps(seal,indent=2)+'\n')
# Read-only exact-set verification. All writes stop after the seal.
found={str(p.relative_to(O)) for p in O.rglob('*') if p.is_file()}
assert found=={r['path'] for r in rows}|{'pins.json','FROZEN.json'}
for r in rows:
 b=(O/r['path']).read_bytes();assert len(b)==r['bytes'] and h(b)==r['sha256']
print(json.dumps({'status':'FROZEN exact-set PASS; WRITE HALT','payload_count':len(rows),'exact_file_count':len(found),'source_records':64,'literal_cuts':32,'files':[{'path':str(O/n),'bytes':(O/n).stat().st_size,'sha256':h((O/n).read_bytes())} for n in ['report-final.md','source-index.json','pins.json','FROZEN.json']]},indent=2))
