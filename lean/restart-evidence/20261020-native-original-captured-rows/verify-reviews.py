import hashlib,json
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
names=['next-original-source-boundary-review-source-pins.json','original-capture-final-review-source-pins.json','original-observed-final-review-source-pins.json','original-terminal-fixture-review-source-pins.json']
checked=0
for name in names:
 data=json.loads((HERE/name).read_text())
 for entry in data.get('files',[]):
  content=(ROOT/entry['path']).read_bytes()
  assert len(content)==entry['bytes'] and hashlib.sha256(content).hexdigest()==entry['sha256'],entry['path']
  checked+=1
 for entry in data.get('candidate_files',[])+data.get('evidence_files',[]):
  folders={'/tmp/mcfta-native-original-row-terminals':'original-row-terminals','/tmp/mcfta-native-original-captured-fixture':'original-captured-fixture','/tmp/mcfta-native-original-terminal-fixture':'original-terminal-fixture'}
  content=(HERE/folders[entry['base']]/entry['path']).read_bytes()
  assert len(content)==entry['bytes'] and hashlib.sha256(content).hexdigest()==entry['sha256'],entry['path']
  checked+=1
print(json.dumps({'status':'PASS','reviews':len(names),'source_pins':checked,'lean_jobs':0}))
