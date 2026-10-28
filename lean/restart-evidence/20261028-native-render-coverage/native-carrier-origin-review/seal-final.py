from pathlib import Path
from datetime import datetime
import hashlib,json
O=Path('/tmp/mcfta-render-coverage-20261028/native-carrier-origin-review')
assert not (O/'FROZEN.json').exists()
sha=lambda b:hashlib.sha256(b).hexdigest()
def check(rec):
 b=Path(rec['path']).read_bytes();assert len(b)==rec['bytes'] and sha(b)==rec['sha256'],rec['path'];return b
idx=json.loads((O/'source-index.json').read_text())
for rec in idx['sources']:
 original=Path(rec['source']).read_bytes()
 if 'whole' in rec:assert check(rec['whole'])==original,rec['source']
 else:assert len(original)==rec['bytes'] and sha(original)==rec['sha256'],rec['source']
 lines=original.splitlines(keepends=True)
 for cut in rec['cuts']:assert check(cut)==b''.join(lines[cut['first_line']-1:cut['last_line']]),cut['path']
for doc in json.loads((O/'documents/document-reconstruction.json').read_text())['documents']:
 original=Path(doc['source']).read_bytes();old=check(doc['old']);insert=check(doc['insert']);offset=doc['offset']
 assert original==old[:offset]+insert+old[offset:]
 assert len(original)==doc['current_bytes'] and sha(original)==doc['current_sha256']
for p in sorted((O/'checks').iterdir()):
 if not p.is_dir() or not (p/'report.json').exists():continue
 report=json.loads((p/'report.json').read_text());raw=(p/'raw.log').read_bytes()
 assert len(raw)==report['bytes'] and sha(raw)==report['sha256'],str(p)
 if 'source_sha256' in report:
  source_name=Path(report['command'][-1]).name
  matches=list(p.rglob(source_name))
  assert len(matches)==1 and sha(matches[0].read_bytes())==report['source_sha256'],str(p)
assert len(idx['sources'])==39 and sum(len(x['cuts']) for x in idx['sources'])==77
# Validate every payload and create the only two excluded seal files last.
files=sorted(p for p in O.rglob('*') if p.is_file() and p.name not in [])
assert all(not p.is_symlink() for p in files)
assert not (O/'pins.json').exists()
payloads=[{'path':str(p.relative_to(O)),'bytes':p.stat().st_size,'sha256':sha(p.read_bytes())} for p in files]
pins={'format':'exact-payload-set-v1','payload_count':len(payloads),'payloads':payloads,'excluded':['pins.json','FROZEN.json']}
pins_bytes=(json.dumps(pins,indent=2)+'\n').encode();(O/'pins.json').write_bytes(pins_bytes)
seal={'status':'FROZEN','created_at':datetime.now().astimezone().isoformat(),'source_head':'7220dacbb21a21b133a17c7160350dca5f0f2a65','review_result':'CLEAR','report':'report-final.md','report_sha256':sha((O/'report-final.md').read_bytes()),'pins_sha256':sha(pins_bytes),'payload_count':len(payloads),'exact_file_count':len(payloads)+2,'source_identities':39,'literal_cuts':77,'write_halt':True}
seal_bytes=(json.dumps(seal,indent=2)+'\n').encode();(O/'FROZEN.json').write_bytes(seal_bytes)
actual=sorted(str(p.relative_to(O)) for p in O.rglob('*') if p.is_file());expected=sorted([p['path'] for p in payloads]+['pins.json','FROZEN.json'])
assert actual==expected
for p in payloads:assert sha((O/p['path']).read_bytes())==p['sha256']
print(json.dumps({**seal,'FROZEN_sha256':sha(seal_bytes)},indent=2))
