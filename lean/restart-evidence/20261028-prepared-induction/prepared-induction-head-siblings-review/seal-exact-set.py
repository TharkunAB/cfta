from pathlib import Path
import hashlib,json,datetime
O=Path('/tmp/mcfta-prepared-induction-20261028/prepared-induction-head-siblings-review')
assert not (O/'pins.json').exists() and not (O/'FROZEN.json').exists()
def sha(b):return hashlib.sha256(b).hexdigest()
payloads=[]
for p in sorted(O.rglob('*')):
 assert not p.is_symlink(),p
 if p.is_file():
  assert p.name not in ['FROZEN.json','pins.json'],p
  b=p.read_bytes();payloads.append({'path':str(p.relative_to(O)),'bytes':len(b),'sha256':sha(b)})
manifest={'payloads':payloads}
b=(json.dumps(manifest,indent=2)+'\n').encode()
seal={'status':'FROZEN','sealed_at':datetime.datetime.now().astimezone().isoformat(),'pins_file':'pins.json','pins_bytes':len(b),'pins_sha256':sha(b),'payload_count':len(payloads),'exact_file_count':len(payloads)+2}
(O/'pins.json').write_bytes(b)
(O/'FROZEN.json').write_text(json.dumps(seal,indent=2)+'\n')
# Read-only verification after the seal. No subsequent writes are permitted.
actual={str(p.relative_to(O)) for p in O.rglob('*') if p.is_file()}
assert actual=={r['path'] for r in payloads}|{'pins.json','FROZEN.json'}
for r in payloads:
 b=(O/r['path']).read_bytes();assert len(b)==r['bytes'] and sha(b)==r['sha256']
assert len(actual)==seal['exact_file_count']
print(json.dumps({'status':'FROZEN exact-set PASS; WRITE HALT','payload_count':len(payloads),'exact_file_count':len(actual),'source_records':101,'literal_cuts':58,'files':[{'path':str(O/n),'bytes':(O/n).stat().st_size,'sha256':sha((O/n).read_bytes())} for n in ['report-final.md','source-index.json','pins.json','FROZEN.json']]},indent=2))
