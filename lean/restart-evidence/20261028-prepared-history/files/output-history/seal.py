from pathlib import Path
from datetime import datetime
import hashlib,json
own=Path('/tmp/mcfta-prepared-history-20261028/output-history')
def sha(b):return hashlib.sha256(b).hexdigest()
def identity(p):
 b=p.read_bytes();return {'path':str(p.relative_to(own)),'bytes':len(b),'sha256':sha(b)}
assert not (own/'pins.json').exists() and not (own/'FROZEN.json').exists()
assert not any(p.is_symlink() for p in own.rglob('*'))
idx=json.loads((own/'source-index.json').read_text())
for s in idx['sources']:
 b=(own/s['whole']['path']).read_bytes();assert b==Path(s['source']).read_bytes();assert (len(b),sha(b))==(s['whole']['bytes'],s['whole']['sha256'])
 lines=b.splitlines(keepends=True)
 for c in s['cuts']:
  cb=(own/c['path']).read_bytes();assert 1<=c['first_line']<=c['last_line']<=len(lines)
  assert cb==b''.join(lines[c['first_line']-1:c['last_line']]);assert (len(cb),sha(cb))==(c['bytes'],c['sha256'])
for record in json.loads((own/'document-inverses-final.json').read_text())['documents']:
 old=(own/record['prior']['path']).read_bytes();insert=(own/record['insert']['path']).read_bytes();off=record['insert_offset'];current=Path(record['source']).read_bytes()
 assert current==old[:off]+insert+old[off:]
 assert (len(old),sha(old))==(record['prior']['bytes'],record['prior']['sha256'])
 assert (len(insert),sha(insert))==(record['insert']['bytes'],record['insert']['sha256'])
 assert (len(current),sha(current))==(record['current']['bytes'],record['current']['sha256'])
for c in json.loads((own/'command-verification-final.json').read_text())['commands']:
 raw=(own/c['raw']).read_bytes();assert (len(raw),sha(raw))==(c['bytes'],c['sha256'])
 r=json.loads((own/c['report']).read_text());assert r['exit_code']==c['exit_code'];assert r['cgroup_limits']=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
pub=json.loads((own/'public-read-scopes-v1.json').read_text());raw=(own/'commands-final/public-readback-final/raw.log').read_bytes()
for block in pub['blocks']:
 b=(own/block['path']).read_bytes();assert b==raw[block['raw_first_byte']:block['raw_last_byte_exclusive']];assert (len(b),sha(b))==(block['bytes'],block['sha256'])
assert (own/'cuts/entire-original-prepared-head-declaration.lean').read_bytes()==(own/'cuts/entire-prepared-head-declaration-recovered.lean').read_bytes()
payloads=[identity(p) for p in sorted(own.rglob('*')) if p.is_file() and p.name not in ['pins.json','FROZEN.json']]
(own/'pins.json').write_text(json.dumps({'payloads':payloads},indent=2)+'\n')
pins=(own/'pins.json').read_bytes()
seal={'status':'FROZEN','review':'CLEAR within bounded assigned scope; whole prepared history resource and semantic composition remains open','frozen_at':datetime.now().astimezone().isoformat(),'pins_path':'pins.json','pins_bytes':len(pins),'pins_sha256':sha(pins),'payload_count':len(payloads),'exact_file_count':len(payloads)+2,'source_wholes':len(idx['sources']),'literal_source_cuts':sum(len(s['cuts']) for s in idx['sources']),'write_halt':True}
(own/'FROZEN.json').write_text(json.dumps(seal,indent=2)+'\n')
# Read-only verification follows. No file changes after FROZEN.json.
actual={str(p.relative_to(own)) for p in own.rglob('*') if p.is_file()}
assert actual=={r['path'] for r in payloads}|{'pins.json','FROZEN.json'}
for r in payloads:
 b=(own/r['path']).read_bytes();assert (len(b),sha(b))==(r['bytes'],r['sha256'])
assert sha((own/'pins.json').read_bytes())==seal['pins_sha256']
print(json.dumps({'status':'FROZEN; WRITE HALT','report':identity(own/'report-final.md'),'pins':identity(own/'pins.json'),'seal':identity(own/'FROZEN.json'),'payload_count':len(payloads),'exact_file_count':len(actual),'source_wholes':len(idx['sources']),'literal_source_cuts':sum(len(s['cuts']) for s in idx['sources'])},indent=2))
