import hashlib, json
from pathlib import Path
root=Path('/home/tritlo/Code/mcfta')
here=Path(__file__).resolve().parent
manifest_path=here/'upstream-review-source-pins.json'
manifest=json.loads(manifest_path.read_text())
for entry in manifest['files']:
 path=root/entry['path']
 assert path.stat().st_size==entry['bytes'], entry['path']
 assert hashlib.sha256(path.read_bytes()).hexdigest()==entry['sha256'], entry['path']
archive=json.loads((here/'upstream-review-source-archive.json').read_text())
source=here/archive['archived_evidence_path']
assert source.stat().st_size==archive['bytes']
assert hashlib.sha256(source.read_bytes()).hexdigest()==archive['sha256']
assert not (here/archive['original_evidence_path']).exists()
for index in range(1,8):
 name=f'upstream-review-binders-{index}'
 receipt=json.loads((here/(name+'.json')).read_text())
 limits=json.loads((here/(name+'.limits.json')).read_text())
 assert limits=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}, name
 assert receipt['exit_code']==(134 if index==7 else 1), name
 assert receipt['source_sha256']==archive['sha256'], name
 assert receipt['wrapper'][1:5]==['--mem','4G','--time','5m'], name
log=(here/'upstream-review-binders-7.log').read_text()
assert 'stack smashing detected' in log
assert 'REPRODUCED:' not in log
assert 'Binders 0 large rank:' not in log
assert len((here/'upstream-review-peaks-final.txt').read_text().splitlines())==7
assert not any(here.glob('upstream-review*.hs'))
print(json.dumps({'status':'PASS','scope':'Archive integrity and effective caps only. No successful Haskell repro.','files':len(manifest['files']),'retained_attempts':7,'successful_repros':0,'lean_jobs':0,'live_jobs':0,'manifest_sha256':hashlib.sha256(manifest_path.read_bytes()).hexdigest()},indent=2))
