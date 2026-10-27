from pathlib import Path
import hashlib,json
from datetime import datetime
out=Path('/tmp/mcfta-continuation-coverage-20261027/hook-policy-review');sha=lambda b:hashlib.sha256(b).hexdigest()
assert not (out/'pins.json').exists() and not (out/'FROZEN.json').exists()
index=json.loads((out/'source-index.json').read_text())
for row in index['sources']:
 live=Path(row['source']).read_bytes();whole=row['whole'];copy=(out/whole['path']).read_bytes();assert live==copy and len(copy)==whole['bytes'] and sha(copy)==whole['sha256'],row['source']
 for cut in row['cuts']:
  b=(out/cut['path']).read_bytes();assert b==b''.join(live.splitlines(keepends=True)[cut['first_line']-1:cut['last_line']]);assert len(b)==cut['bytes'] and sha(b)==cut['sha256']
docs=json.loads((out/'documents/independent-validation.json').read_text())
for row in docs['documents']:
 b=(out/row['current']['path']).read_bytes();assert b==Path(row['document_source_path']).read_bytes()
 if 'insertion' in row:
  old=(out/row['prior']['path']).read_bytes();i=(out/row['insertion']['path']).read_bytes();at=row['insertion']['byte_offset'];assert b[at:at+len(i)]==i and b[:at]+b[at+len(i):]==old
for p in out.rglob('*'):assert not p.is_symlink(),p
files=sorted(p for p in out.rglob('*') if p.is_file());assert all(p.name not in ['pins.json','FROZEN.json'] for p in files)
payloads=[{'path':str(p.relative_to(out)),'bytes':p.stat().st_size,'sha256':sha(p.read_bytes())} for p in files]
pins=json.dumps({'payloads':payloads},indent=2)+'\n';(out/'pins.json').write_text(pins)
seal={'status':'FROZEN','sealed_at':datetime.now().astimezone().isoformat(timespec='seconds'),'source_head':'0684e0b726efa04c1063f0f71b24d58d77ffbea6','pins':'pins.json','pins_sha256':sha(pins.encode()),'payload_count':len(payloads),'exact_file_count':len(payloads)+2,'review_verdict':'CLEAR','source_records':len(index['sources']),'literal_cuts':sum(len(r['cuts']) for r in index['sources']),'all_writes_stopped':True}
(out/'FROZEN.json').write_text(json.dumps(seal,indent=2)+'\n')
print(json.dumps({'seal':seal,'FROZEN_sha256':sha((out/'FROZEN.json').read_bytes())},indent=2))
