from pathlib import Path
import json,hashlib,subprocess
p=Path('/tmp/mcfta-prepared-origins-20261028/child-origins')
a=p.parent
sha=lambda b:hashlib.sha256(b).hexdigest()
assert not (p/'FROZEN.json').exists()
idx=json.loads((p/'source-index.json').read_text())
for rec in idx['sources']:
 b=Path(rec['source']).read_bytes();lines=b.splitlines(keepends=True)
 if 'whole' in rec:
  w=rec['whole'];assert (p/w['path']).read_bytes()==b and w['bytes']==len(b) and w['sha256']==sha(b)
 if 'whole_identity' in rec:
  w=rec['whole_identity'];assert w['bytes']==len(b) and w['sha256']==sha(b)
 for c in rec['cuts']:
  data=b''.join(lines[c['first_line']-1:c['last_line']]);assert (p/c['path']).read_bytes()==data and c['bytes']==len(data) and c['sha256']==sha(data)
for report in (p/'checks').glob('*/report.json'):
 r=json.loads(report.read_text());b=(report.parent/'raw.log').read_bytes();assert r['bytes']==len(b) and r['sha256']==sha(b)
 assert r['cgroup_limits']=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
full=(p/'checks/public-readback-final/raw.log').read_bytes();old=(p/'checks/prior-public-readback/raw.log').read_bytes()
assert full.startswith(old) and len(full)==2015663 and len(old)==1902411
for rec in json.loads((p/'evidence/public-review.json').read_text())['whole_assigned_blocks_read']:
 b=(p/'public-blocks'/f"{rec['declaration']}.txt").read_bytes()
 assert b==full[len(old)+rec['offset']:len(old)+rec['offset']+rec['bytes']] and sha(b)==rec['sha256']
for rec in json.loads((p/'documents/document-verification.json').read_text())['nine_exact_insertions_verified']:
 b=Path(rec['source']).read_bytes();off=rec['insertion_offset'];n=rec['inserted_bytes'];prior=(a/'prior-documents'/rec['path']).read_bytes()
 assert b[:off]+b[off+n:]==prior and sha(b)==rec['whole_sha256'] and sha(prior)==rec['prior_sha256']
assert (p/'contracts/original-child-declaration.txt').read_bytes()==(p/'contracts/recovered-child-declaration-v1.txt').read_bytes()
assert (p/'contracts/root-opaque-original-resource-declaration.txt').read_bytes()==(p/'contracts/root-opaque-recovered-resource-declaration-v1.txt').read_bytes()
for q in p.rglob('*'):assert not q.is_symlink()
now=subprocess.check_output(['date','+%Y-%m-%d %H:%M:%S %Z'],text=True).strip()
verification={'status':'PASS','measured_at':now,'source_records':len(idx['sources']),'literal_cuts':sum(len(x['cuts']) for x in idx['sources']),'whole_assigned_public_blocks':3,'document_inverse_bodies':9,'current_commands':19,'inherited_receipts':1,'current_failures_retained':2,'proof_or_runtime_commands_run_by_reviewer':0,'all_live_whole_and_literal_source_identities_match':True,'both_entire_old_declarations_recovered':True,'scope':'Read-only byte/hash verification. Entire old giant document bodies were recovered, not read.'}
(p/'verification-final.json').write_text(json.dumps(verification,indent=2)+'\n')
files=sorted(q for q in p.rglob('*') if q.is_file() and q.name not in [])
assert not any(q.relative_to(p).as_posix() in ['pins.json','FROZEN.json'] for q in files)
payloads=[{'path':q.relative_to(p).as_posix(),'bytes':q.stat().st_size,'sha256':sha(q.read_bytes())} for q in files]
pins=(json.dumps({'payloads':payloads},indent=2)+'\n').encode();(p/'pins.json').write_bytes(pins)
seal={'status':'FROZEN','measured_at':now,'pins':'pins.json','pins_bytes':len(pins),'pins_sha256':sha(pins),'payload_count':len(payloads),'exact_file_count':len(payloads)+2,'write_halt':True}
sealed=(json.dumps(seal,indent=2)+'\n').encode();(p/'FROZEN.json').write_bytes(sealed)
# Read-only verification after seal. No file is created after this point.
assert len([q for q in p.rglob('*') if q.is_file()])==len(payloads)+2
assert {q.relative_to(p).as_posix() for q in p.rglob('*') if q.is_file()}=={x['path'] for x in payloads}|{'pins.json','FROZEN.json'}
for rec in payloads:
 b=(p/rec['path']).read_bytes();assert len(b)==rec['bytes'] and sha(b)==rec['sha256']
assert sha((p/'pins.json').read_bytes())==seal['pins_sha256']
print(json.dumps({'status':'FROZEN/WRITE HALT','payload_count':len(payloads),'exact_file_count':len(payloads)+2,'source_records':len(idx['sources']),'literal_cuts':verification['literal_cuts'],'identities':[{ 'path':str(p/n),'bytes':len((p/n).read_bytes()),'sha256':sha((p/n).read_bytes())} for n in ['report-final.md','pins.json','FROZEN.json']]},indent=2))
