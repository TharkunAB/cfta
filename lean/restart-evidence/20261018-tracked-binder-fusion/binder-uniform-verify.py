import hashlib,json,runpy
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
read=lambda n:json.loads((HERE/n).read_text())
for e in read('binder-uniform-manifest.json')['entries']:
 assert hashlib.sha256((ROOT/e['path']).read_bytes()).hexdigest()==e['sha256'],e['path']
c=runpy.run_path(str(HERE/'verify-probes.py'));s=read('binder-uniform-selection.json')
for g in s['groups']:c['check_group'](g)
r=read(s['constructed_strict']+'.json');assert r['exit_code']==0 and not (HERE/r['log']).read_bytes();c['check_limits'](s['constructed_strict'])
assert (HERE/r['source']).read_bytes()==(HERE/'binder-uniform-kernels.lean').read_bytes()
assert (HERE/r['source']).read_bytes().startswith((HERE/'binder-contract-direct-5.source.lean').read_bytes())
print(json.dumps({'status':'PASS','constructed_pairs':1,'new_production':0,'all_positive_uniform_bounds_refuted':True,'pins':len(read('binder-uniform-manifest.json')['entries'])}))
