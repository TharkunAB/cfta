import hashlib,json,runpy
from pathlib import Path
H=Path(__file__).resolve().parent
R=H.parents[2]
pins=json.loads((H/'math-review-source-pins.json').read_text())['files']
for item in pins:
 data=(R/item['path']).read_bytes()
 assert len(data)==item['bytes'] and hashlib.sha256(data).hexdigest()==item['sha256'],item['path']
v=runpy.run_path(str(H/'verify-probes.py'),run_name='math_review_reuse')
for stem,pairs in [('head-public-1',5),('head-kernels-public-1',1)]:
 v['check_group']({'name':stem,'pairs':pairs,'full_proof':True})
for stem,source in [('head-direct-3',R/'lean/MicroCFTA/SourceCurrentRecursiveHeadMuChildContexts.lean'),('head-kernels-direct-2',H/'head-kernels.lean')]:
 meta=json.loads((H/(stem+'.json')).read_text())
 assert meta['exit_code']==0 and not (H/meta['log']).read_bytes(),stem
 assert (H/meta['source']).read_bytes()==source.read_bytes(),stem
 v['check_limits'](stem)
for stem in ['head-direct-3','head-kernels-direct-2','head-canonical-1','head-public-1','head-kernels-public-1']:
 meta=json.loads((H/(stem+'.json')).read_text())
 assert meta['exit_code']==0,stem
 v['check_limits'](stem)
 assert meta['wrapper'][meta['wrapper'].index('--time')+1]=='5m',stem
 if 'source' in meta: assert hashlib.sha256((H/meta['source']).read_bytes()).hexdigest()==meta['sha256'],stem
print(json.dumps({'status':'PASS','pins':len(pins),'new_proof_pairs':0,'new_lean_runs':0,'reused_public_pairs':5,'reused_constructed_pairs':1},indent=2))
