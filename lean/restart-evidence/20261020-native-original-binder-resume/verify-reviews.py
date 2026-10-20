import hashlib,json
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
NAMES=['binder-plan-review','binder-final-review','binder-fixture-review']
def check(path,entry):
 data=path.read_bytes()
 assert len(data)==entry['bytes'] and hashlib.sha256(data).hexdigest()==entry['sha256'],str(path)
checked=0
for name in NAMES:
 data=json.loads((HERE/(name+'-source-pins.json')).read_text())
 check(HERE/(name+'.md'),data['review'])
 for entry in data.get('files',[]):
  check(ROOT/entry['path'],entry);checked+=1
 for entry in data.get('candidate_files',[])+data.get('historical_files',[]):
  check(HERE/'binder-resume-reviewed-draft.lean',entry);checked+=1
 for entry in data.get('evidence_files',[]):
  check(HERE/'prior-selected-binder-resume-fixture.lean',entry);checked+=1
 for entry in data.get('fixture_files',[]):
  check(HERE/'binder-fixture'/entry['path'],entry);checked+=1
 assert data['counts']['new_jobs']==data['counts']['owned_pairs']==0
 if name=='binder-fixture-review':
  assert data['counts']['reused_constructed_pairs']==data['counts']['examples']==1
 else:
  assert data['counts']['reused_pairs']==0
print(json.dumps({'status':'PASS','reviews':len(NAMES),'source_and_evidence_pins':checked,'lean_jobs':0}))
