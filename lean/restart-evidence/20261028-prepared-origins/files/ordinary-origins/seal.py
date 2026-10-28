from pathlib import Path
import hashlib,json,datetime
out=Path(__file__).resolve().parent
assert not (out/'FROZEN.json').exists()
assert json.loads((out/'verification.json').read_text())['status']=='PASS'
def sha(b): return hashlib.sha256(b).hexdigest()
paths=sorted(p for p in out.rglob('*') if p.is_file() and p.relative_to(out).as_posix() not in ['pins.json','FROZEN.json'])
payloads=[{'path':p.relative_to(out).as_posix(),'bytes':p.stat().st_size,'sha256':sha(p.read_bytes())}for p in paths]
pins={'payloads':payloads}; pinbytes=(json.dumps(pins,indent=2)+'\n').encode(); (out/'pins.json').write_bytes(pinbytes)
seal={'pins_file':'pins.json','pins_bytes':len(pinbytes),'pins_sha256':sha(pinbytes),'payload_count':len(payloads),'exact_file_count':len(payloads)+2}
sealbytes=(json.dumps(seal,indent=2)+'\n').encode();(out/'FROZEN.json').write_bytes(sealbytes)
actual={p.relative_to(out).as_posix() for p in out.rglob('*')if p.is_file()}
assert actual=={r['path']for r in payloads}|{'pins.json','FROZEN.json'}
for r in payloads:
 b=(out/r['path']).read_bytes();assert len(b)==r['bytes']and sha(b)==r['sha256']
assert (out/'pins.json').read_bytes()==pinbytes and (out/'FROZEN.json').read_bytes()==sealbytes
print(json.dumps({'status':'SEALED; WRITE HALT','time':datetime.datetime.now().astimezone().strftime('%Y-%m-%d %H:%M:%S %Z'),'seal':seal,'pins_sha256':sha(pinbytes),'FROZEN_sha256':sha(sealbytes),'FROZEN_bytes':len(sealbytes),'report_path':str(out/'report.txt'),'report_bytes':(out/'report.txt').stat().st_size,'report_sha256':sha((out/'report.txt').read_bytes())},indent=2))
