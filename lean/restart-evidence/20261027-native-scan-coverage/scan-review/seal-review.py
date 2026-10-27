from pathlib import Path
import hashlib,json
from datetime import datetime
out=Path('/tmp/mcfta-native-scan-coverage-20261027/scan-review');sha=lambda b:hashlib.sha256(b).hexdigest()
assert not (out/'pins.json').exists() and not (out/'FROZEN.json').exists()
index=json.loads((out/'source-index.json').read_text())
for row in index['sources']:
 live=Path(row['source']).read_bytes();whole=row['whole'];copy=(out/whole['path']).read_bytes()
 assert live==copy and len(copy)==whole['bytes'] and sha(copy)==whole['sha256'],row['source']
 for cut in row['cuts']:
  c=(out/cut['path']).read_bytes();assert c==b''.join(live.splitlines(keepends=True)[cut['first_line']-1:cut['last_line']]);assert len(c)==cut['bytes'] and sha(c)==cut['sha256']
docs=json.loads((out/'documents/independent-validation.json').read_text())
for row in docs['documents']:
 current=(out/row['current']['path']).read_bytes();assert current==Path(row['document_source_path']).read_bytes()
 if 'insertion' in row:
  old=(out/row['prior']['path']).read_bytes();ins=(out/row['insertion']['path']).read_bytes();at=row['insertion']['byte_offset'];assert current[at:at+len(ins)]==ins and current[:at]+current[at+len(ins):]==old
for p in out.rglob('*'):
 assert not p.is_symlink(),p
files=sorted(p for p in out.rglob('*') if p.is_file());assert all(p.name not in ['pins.json','FROZEN.json'] for p in files)
payloads=[{'path':str(p.relative_to(out)),'bytes':p.stat().st_size,'sha256':sha(p.read_bytes())} for p in files]
pins=json.dumps({'payloads':payloads},indent=2)+'\n';(out/'pins.json').write_text(pins)
seal={'status':'FROZEN','sealed_at':datetime.now().astimezone().isoformat(timespec='seconds'),'source_head':'8368460445fe4b05073a1bf134e9e34e190f2282','pins':'pins.json','pins_sha256':sha(pins.encode()),'payload_count':len(payloads),'exact_file_count':len(payloads)+2,'review_verdict':'CLEAR','source_records':len(index['sources']),'literal_cuts':sum(len(r['cuts']) for r in index['sources']),'all_writes_stopped':True}
(out/'FROZEN.json').write_text(json.dumps(seal,indent=2)+'\n')
print(json.dumps({'seal':seal,'FROZEN_sha256':sha((out/'FROZEN.json').read_bytes())},indent=2))
