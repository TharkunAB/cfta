from pathlib import Path
from datetime import datetime
from zoneinfo import ZoneInfo
import hashlib,json,shutil
A=Path('/tmp/mcfta-history-checked-origins-20261027');O=A/'history-origin-transport-review';R=Path('/home/tritlo/Code/mcfta')
def sha(d):return hashlib.sha256(d).hexdigest()
def save(rel,d):
 p=O/rel;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(d);return {'snapshot':str(p),'bytes':len(d),'sha256':sha(d)}
def put(rel,x):return save(rel,(json.dumps(x,indent=2)+'\n').encode())
assert not (O/'FROZEN').exists();h=O/'review-revisions/before-build-seal';h.mkdir(parents=True,exist_ok=True)
for n in ['report.txt','source-index.json','verification.json','OPEN.json']:
 assert not (h/n).exists();shutil.copyfile(O/n,h/n)
records=json.loads((O/'source-index.json').read_text())['sources'];name='SourcePruningEnumerationAllocatedOriginHeap';parts={}
for p,rel,scope in [(R/f'lean/MicroCFTA/{name}.lean',f'installed/{name}.lean','whole installed source byte-equal to reviewed/strict final v2'),(A/'build-origin-interfaces-1/report.json','actual-build/report.json','whole actual successful capped build report read'),(A/'build-origin-interfaces-1/raw.log','actual-build/raw.log','whole actual successful1962job build output read, old unused-input warning retained')]:
 d=p.read_bytes();parts[rel]=d;records.append({'source':str(p),**save(rel,d),'scope':'whole exact source/evidence identity','reviewed_scope':scope,'cuts':[]})
assert parts[f'installed/{name}.lean']==(O/f'drafts/v2/{name}.lean').read_bytes()
r=json.loads(parts['actual-build/report.json']);raw=parts['actual-build/raw.log'];assert r['exit_code']==0 and len(raw)==r['bytes']==812 and sha(raw)==r['sha256'] and b'1962 jobs' in raw;assert r['cgroup_limits']=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
now=datetime.now(ZoneInfo('Europe/Stockholm')).isoformat();previous=(O/'report.txt').read_text();paragraph=f'''\n[{now}] Final bounded integration receipt / CLEAR.

Root installed final v2 byte-exact and build-origin-interfaces-1 PASS1962jobs/812B at actual4GiB/swap0. Its older unused-input warning is retained. This build includes the actual constructor Heap module and interface consumers. The bounded constructor implementation/review is complete and now sealed at Root's request. The surrounding checkpoint remains OPEN for its final native-body source, public/Audit/document claims. Those later claims belong to a separate origin-checkpoint-review and are not asserted by this seal. No global query/history Heap preservation is claimed. All prior drafts/failure/strict success/header mappings, exact source inputs and transport plan remain retained.\n''';save('report.txt',(previous+paragraph).encode())
put('source-index.json',{'schema':'whole sources and explicit literal cuts','cut_convention':'one-based inclusive; splitlines(keepends=True); original LF retained','sources':records});checks=0
for rec in records:
 d=Path(rec['source']).read_bytes();assert d==Path(rec['snapshot']).read_bytes() and len(d)==rec['bytes'] and sha(d)==rec['sha256'];checks+=1
 for c in rec['cuts']:
  part=b''.join(d.splitlines(keepends=True)[c['first_line']-1:c['last_line']]);assert part==Path(c['snapshot']).read_bytes() and len(part)==c['bytes'] and sha(part)==c['sha256'];checks+=1
put('verification.json',{'status':'PASS','checked_at':now,'source_records':len(records),'literal_cuts':sum(len(x['cuts']) for x in records),'byte_checks':checks,'final_strict2_pass':True,'installed_byte_exact':True,'build_origin_interfaces_1962_pass':True,'initial_failure_retained':True,'all_four_declaration_headers_exact':True,'scope':'bounded constructor invariant proof; overall checkpoint/public/Audit/docs not asserted'})
(O/'OPEN.json').unlink()
files={str(p.relative_to(O)):{'bytes':len(p.read_bytes()),'sha256':sha(p.read_bytes())} for p in sorted(O.rglob('*')) if p.is_file()}
put('pins.json',{'schema':'frozen-payload-files','payload_count':len(files),'file_count_including_pins':len(files)+1,'files':files});pin=(O/'pins.json').read_bytes();report=(O/'report.txt').read_bytes();index=(O/'source-index.json').read_bytes();put('FROZEN',{'status':'CLEAR / FROZEN','frozen_at':now,'payload_count':len(files),'exact_file_count':len(files)+2,'pins_bytes':len(pin),'pins_sha256':sha(pin),'report_sha256':sha(report),'source_index_sha256':sha(index),'source_records':len(records),'literal_cuts':sum(len(x['cuts']) for x in records),'byte_checks':checks,'scope':'constructor invariant source/strict/installed/build plus next transport plan; overall area NOT frozen'})
assert len([p for p in O.rglob('*') if p.is_file()])==len(files)+2
for rel,v in files.items():
 d=(O/rel).read_bytes();assert len(d)==v['bytes'] and sha(d)==v['sha256']
print(json.dumps({'status':'CLEAR / FROZEN bounded review only','payloads':len(files),'exact_files':len(files)+2,'source_records':len(records),'literal_cuts':sum(len(x['cuts']) for x in records),'byte_checks':checks,'FROZEN_sha256':sha((O/'FROZEN').read_bytes()),'pins_sha256':sha(pin),'report_sha256':sha(report),'source_index_sha256':sha(index)},indent=2))
