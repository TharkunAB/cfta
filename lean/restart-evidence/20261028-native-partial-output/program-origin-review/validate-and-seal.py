from pathlib import Path
from datetime import datetime
import hashlib,json
O=Path('/tmp/mcfta-native-partial-output-20261028/program-origin-review')
assert not(O/'pins.json').exists() and not(O/'FROZEN.json').exists()
sha=lambda b:hashlib.sha256(b).hexdigest()
def checked(rec):
 p=Path(rec['path']);p=p if p.is_absolute() else O/p;b=p.read_bytes()
 assert len(b)==rec['bytes'] and sha(b)==rec['sha256'],p
 return b
sources=json.loads((O/'source-index.json').read_text())['sources'];cuts=0;docs=0
for s in sources:
 original=Path(s['source']).read_bytes()
 if 'whole' in s:assert checked(s['whole'])==original
 else:assert len(original)==s['bytes'] and sha(original)==s['sha256']
 for c in s['cuts']:
  data=checked(c)
  expected=b''.join(original.splitlines(keepends=True)[c['first_line']-1:c['last_line']]) if 'first_line' in c else original[c['byte_start']:c['byte_end']]
  assert data==expected,(s['source'],c['path']);cuts+=1
 if 'reconstruction' in s:
  r=s['reconstruction'];before=checked(r['prior']);insert=checked(r['insert']);n=r['offset']
  assert before[:n]+insert+before[n:]==original;docs+=1
assert len(sources)==117 and cuts==60 and docs==9
report=O/'report-final.md';validation={'status':'pass','source_identities':len(sources),'literal_cuts':cuts,'document_reconstructions':docs,'all_originals_wholes_cuts_exact':True,'report_bytes':report.stat().st_size,'report_sha256':sha(report.read_bytes()),'review_scope':'All six final sources, all nine full new theorem/axiom blocks and three runtime definitions, whole final note and all nine inserted regions; historical large document bodies inverse-only.'}
(O/'final-validation.json').write_text(json.dumps(validation,indent=2)+'\n')
files=sorted(p for p in O.rglob('*') if p.is_file());assert all(not p.is_symlink() for p in O.rglob('*'))
assert not any(p.suffix in {'.pyc','.olean','.ilean'} or '__pycache__' in p.parts for p in files)
payloads=[]
for p in files:
 assert p.name not in {'pins.json','FROZEN.json'}
 b=p.read_bytes();payloads.append({'path':str(p.relative_to(O)),'bytes':len(b),'sha256':sha(b)})
(O/'pins.json').write_text(json.dumps({'payload_count':len(payloads),'payloads':payloads},indent=2)+'\n');pins=(O/'pins.json').read_bytes()
seal={'status':'FROZEN; WRITE HALT','created_at':datetime.now().astimezone().isoformat(timespec='seconds'),'pins':'pins.json','pins_bytes':len(pins),'pins_sha256':sha(pins),'payload_count':len(payloads),'exact_file_count':len(payloads)+2,'report':'report-final.md','report_sha256':sha(report.read_bytes()),'source_head':'d4d4260e20d7bc3d003c8779256475254fcedcc5'}
(O/'FROZEN.json').write_text(json.dumps(seal,indent=2)+'\n')
# Only read after the seal. No further writes are allowed in this subtree.
assert {p['path'] for p in payloads}|{'pins.json','FROZEN.json'}=={str(p.relative_to(O)) for p in O.rglob('*') if p.is_file()}
for p in payloads:checked(p)
assert len((O/'pins.json').read_bytes())==seal['pins_bytes'] and sha((O/'pins.json').read_bytes())==seal['pins_sha256']
print(json.dumps({'status':'CLEAR; SEALED; WRITE HALT','report':str(report),'report_bytes':report.stat().st_size,'report_sha256':sha(report.read_bytes()),'source_identities':len(sources),'literal_cuts':cuts,'doc_inverses':docs,'payload_count':len(payloads),'exact_file_count':len(payloads)+2,'pins_bytes':len(pins),'pins_sha256':sha(pins),'seal_sha256':sha((O/'FROZEN.json').read_bytes()),'created_at':seal['created_at']},indent=2))
