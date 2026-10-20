import argparse,hashlib,json
from pathlib import Path
HERE=Path(__file__).resolve().parent
p=argparse.ArgumentParser();p.add_argument('--root',type=Path,required=True);p.add_argument('--live',action='store_true');a=p.parse_args()
def check(base,item):
 b=(base/item['path']).read_bytes();assert len(b)==item['bytes'] and hashlib.sha256(b).hexdigest()==item['sha256'],item['path']
m=json.loads((HERE/'manifest.json').read_text())
for x in m['files']:check(HERE,x)
r=json.loads((HERE/'source-pins.json').read_text())['files']
for x in r:check(a.root,x)
d=json.loads((HERE/'mcfta-next-active-mu-row-design.source-pins.json').read_text())['files']
for x in d:check(a.root,x)
if a.live:
 for x in m['reviewed_sources']:assert (HERE/x['local']).read_bytes()==(a.root/x['root']).read_bytes()
stored=(HERE/'SourceCurrentNativeCapturedMuStoredRows.lean').read_text()
unfold=(HERE/'SourceCurrentNativeCapturedMuUnfoldRows.lean').read_text()
assert stored.count('SourceCurrentNativeCapturedMuRowProduction.capture ')==1
assert unfold.count('SourceCurrentNativeCapturedMuStoredRows.capture ')==1
assert unfold.count('SourceCurrentNativePublicationTrace.from_history ')==1
print(json.dumps({'status':'PASS','pins':len(m['files'])+len(r),'preserved_design_dependency_pins':len(d),'new_lean_jobs':0,'owned_pairs':0,'reused_pairs':0,'reviewed_sources':3,'mode':'live' if a.live else 'ordinary'}))
