from pathlib import Path
from datetime import datetime
from zoneinfo import ZoneInfo
import hashlib,json
O=Path('/tmp/mcfta-history-boundary-exclusion-20261027/gates-review')
def sha(d):return hashlib.sha256(d).hexdigest()
def put(name,obj):(O/name).write_text(json.dumps(obj,indent=2,ensure_ascii=False)+'\n')
assert not (O/'FROZEN').exists() and not (O/'pins.json').exists()
# Final exact identities and literal cuts. Historical versions remain separate records.
index=json.loads((O/'source-index.json').read_text());checks=0
for rec in index['sources']:
 data=Path(rec['source']).read_bytes();assert len(data)==rec['bytes'] and sha(data)==rec['sha256'];checks+=1
 if 'snapshot' in rec:assert data==Path(rec['snapshot']).read_bytes()
 for cut in rec['cuts']:
  part=b''.join(data.splitlines(keepends=True)[cut['first_line']-1:cut['last_line']]);assert len(part)==cut['bytes'] and sha(part)==cut['sha256'] and part==Path(cut['snapshot']).read_bytes();checks+=1
now=datetime.now(ZoneInfo('Europe/Stockholm')).isoformat()
old=O/'OPEN.json';(O/'review-revisions/before-final/OPEN-before-seal.json').write_bytes(old.read_bytes());old.unlink()
put('seal-verification.json',{'status':'PASS','checked_at':now,'source_records':len(index['sources']),'literal_cuts':sum(len(x['cuts']) for x in index['sources']),'byte_checks':checks,'review_status':'CLEAR','scope':'All seven final sources/public/final note/new document regions; exact prior inverses and old public blocks','publication_archive_and_push':'subsequent Root work; not asserted'})
files={str(p.relative_to(O)):{'bytes':len(p.read_bytes()),'sha256':sha(p.read_bytes())} for p in sorted(O.rglob('*')) if p.is_file()}
put('pins.json',{'schema':'frozen-payload-files','payload_count':len(files),'file_count_including_pins':len(files)+1,'files':files})
pins=(O/'pins.json').read_bytes();report=(O/'report.txt').read_bytes();source_index=(O/'source-index.json').read_bytes()
put('FROZEN',{'status':'CLEAR / FROZEN','frozen_at':now,'source_checkpoint':'87f6dee2580ba6b668775a34325b015ff2bfe4d0','payload_count':len(files),'exact_file_count':len(files)+2,'pins_bytes':len(pins),'pins_sha256':sha(pins),'report_sha256':sha(report),'source_index_sha256':sha(source_index),'source_records':len(index['sources']),'literal_cuts':sum(len(x['cuts']) for x in index['sources']),'byte_checks':checks,'publication_status':'archive/publication verification remains Root work after this seal; not asserted'})
# Read-only seal self-check.
assert len(list(p for p in O.rglob('*') if p.is_file()))==len(files)+2
for rel,record in files.items():
 data=(O/rel).read_bytes();assert len(data)==record['bytes'] and sha(data)==record['sha256']
frozen=(O/'FROZEN').read_bytes()
print(json.dumps({'status':'CLEAR / FROZEN','frozen_at':now,'payloads':len(files),'exact_files':len(files)+2,'source_records':len(index['sources']),'literal_cuts':sum(len(x['cuts']) for x in index['sources']),'byte_checks':checks,'pins_sha256':sha(pins),'FROZEN_sha256':sha(frozen),'report_sha256':sha(report),'source_index_sha256':sha(source_index)},indent=2))
