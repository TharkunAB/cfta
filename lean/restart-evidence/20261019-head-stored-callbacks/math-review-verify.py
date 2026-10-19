import hashlib,json,runpy
from pathlib import Path
H=Path(__file__).resolve().parent
R=H.parents[2]
files=json.loads((H/'math-review-source-pins.json').read_text())['files']
for f in files:
 d=(R/f['path']).read_bytes()
 assert len(d)==f['bytes'] and hashlib.sha256(d).hexdigest()==f['sha256'],f['path']
v=runpy.run_path(str(H/'verify-probes.py'),run_name='callback_review')
v['check_group']({'name':'callback-public-1','pairs':4,'full_proof':True})
for stem in ['callback-direct-3','callback-canonical-1','callback-public-1']:
 m=json.loads((H/(stem+'.json')).read_text());assert m['exit_code']==0,stem
 v['check_limits'](stem)
 assert m['wrapper'][m['wrapper'].index('--time')+1]=='5m',stem
 if 'source'in m:assert hashlib.sha256((H/m['source']).read_bytes()).hexdigest()==m['sha256'],stem
m=json.loads((H/'callback-direct-3.json').read_text())
assert not (H/m['log']).read_bytes()
assert (H/m['source']).read_bytes()==(R/'lean/MicroCFTA/SourceCurrentStoredCallbackChildContexts.lean').read_bytes()
print(json.dumps({'status':'PASS','pins':len(files),'new_proof_pairs':0,'new_lean_runs':0,'reused_public_pairs':4,'reused_constructed_pairs':0},indent=2))
