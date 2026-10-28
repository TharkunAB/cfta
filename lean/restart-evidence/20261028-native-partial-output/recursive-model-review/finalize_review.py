from pathlib import Path
from hashlib import sha256
from datetime import datetime
import json

O=Path('/tmp/mcfta-native-partial-output-20261028/recursive-model-review')
assert not (O/'pins.json').exists() and not (O/'FROZEN.json').exists()
idx=json.loads((O/'source-index.json').read_text())
for source in idx['sources']:
    whole=source['whole']
    data=(O/whole['path']).read_bytes()
    assert len(data)==whole['bytes']==source['bytes']
    assert sha256(data).hexdigest()==whole['sha256']==source['sha256']
    lines=data.splitlines(keepends=True)
    for cut in source['cuts']:
        actual=(O/cut['path']).read_bytes()
        assert actual==b''.join(lines[cut['first_line']-1:cut['last_line']])
        assert len(actual)==cut['bytes'] and sha256(actual).hexdigest()==cut['sha256']
        assert cut['source_sha256']==source['sha256']

checks=json.loads((O/'final-evidence-index.json').read_text())
for payload in checks['files']:
    data=(O/payload['path']).read_bytes()
    assert len(data)==payload['bytes'] and sha256(data).hexdigest()==payload['sha256']
assert checks['commands']==17 and checks['failed_commands']==5
assert checks['source_head']=='d4d4260e20d7bc3d003c8779256475254fcedcc5'
assert json.loads((O/'initial-whole-contract-comparison.json').read_text())['literal_equal']
assert json.loads((O/'document-inverse-checks.json').read_text())['status']=='PASS'
# The final report and status are written before the manifest. Nothing in the
# sealed payload tree is changed after its seal.
now=datetime.now().astimezone().isoformat()
status=json.loads((O/'review-status.json').read_text())
status['status']='CLEAR_FINAL'
status['finalized_at']=now
status['write_halt_after_seal']=True
(O/'review-status.json').write_text(json.dumps(status,indent=2)+'\n')
payloads=[]
for path in sorted(O.rglob('*')):
    assert not path.is_symlink(),str(path)
    if not path.is_file(): continue
    rel=path.relative_to(O).as_posix()
    # Exclude only these root files. Nested seals, if any, remain payloads.
    if rel in {'pins.json','FROZEN.json'}: continue
    data=path.read_bytes()
    payloads.append({'path':rel,'bytes':len(data),'sha256':sha256(data).hexdigest()})
manifest={'schema':'payloads-v1','created_at':now,'payload_count':len(payloads),'payloads':payloads}
pins=(json.dumps(manifest,indent=2)+'\n').encode()
(O/'pins.json').write_bytes(pins)
report=(O/'report.txt').read_bytes()
seal={'schema':'review-seal-v1','status':'FROZEN','result':'CLEAR','write_halt':True,
      'sealed_at':now,'source_head':checks['source_head'],
      'pins':'pins.json','pins_bytes':len(pins),'pins_sha256':sha256(pins).hexdigest(),
      'payload_count':len(payloads),'exact_file_count':len(payloads)+2,
      'report':'report.txt','report_bytes':len(report),'report_sha256':sha256(report).hexdigest(),
      'source_index_sha256':sha256((O/'source-index.json').read_bytes()).hexdigest(),
      'publication_scope':'Archive creation, committed archive checks and push are subsequent Root actions; none is asserted here.'}
(O/'FROZEN.json').write_text(json.dumps(seal,indent=2)+'\n')
# Read-only exact-set and hash verification after sealing.
physical={p.relative_to(O).as_posix() for p in O.rglob('*') if p.is_file()}
assert physical=={p['path'] for p in payloads}|{'pins.json','FROZEN.json'}
for p in payloads:
    data=(O/p['path']).read_bytes()
    assert len(data)==p['bytes'] and sha256(data).hexdigest()==p['sha256']
assert sha256((O/'pins.json').read_bytes()).hexdigest()==seal['pins_sha256']
print(json.dumps({'report':str(O/'report.txt'),'pins':str(O/'pins.json'),
    'seal':str(O/'FROZEN.json'),'sealed_at':now,'payload_count':len(payloads),
    'exact_file_count':len(physical),'pins_bytes':len(pins),'pins_sha256':seal['pins_sha256'],
    'report_sha256':seal['report_sha256'],'FROZEN_sha256':sha256((O/'FROZEN.json').read_bytes()).hexdigest(),
    'source_records':len(idx['sources']),'whole_copies':sum('whole' in s for s in idx['sources']),
    'literal_cuts':sum(len(s['cuts']) for s in idx['sources']),
    'status':'CLEAR / FROZEN / WRITE HALT'},indent=2))
