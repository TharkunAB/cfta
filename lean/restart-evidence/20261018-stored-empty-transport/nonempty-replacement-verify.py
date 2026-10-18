import hashlib,json,runpy
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
def read(name): return json.loads((HERE/name).read_text())
for e in read('nonempty-replacement-manifest.json')['entries']:
 p=ROOT/e['path']; assert hashlib.sha256(p.read_bytes()).hexdigest()==e['sha256'],e['path']
s=read('nonempty-replacement-selection.json')
assert read(s['strict']+'.json')['exit_code']==0
assert not (HERE/(s['strict']+'.log')).read_bytes()
assert (HERE/(s['strict']+'.source.lean')).read_bytes()==(ROOT/'lean/MicroCFTA/SourceCurrentStoredNonemptyReplacement.lean').read_bytes()
c=read(s['canonical']+'.json'); assert c['exit_code']==0
l=(HERE/c['log']).read_text(); assert 'Build completed successfully' in l and 'warning:' not in l
checker=runpy.run_path(str(HERE/'verify-probes.py'))
checker['check_limits'](s['strict']);checker['check_limits'](s['canonical'])
for g in s['groups']: checker['check_group'](g)
k=read(s['constructed_strict']+'.json');assert k['exit_code']==0 and not (HERE/k['log']).read_bytes()
assert (HERE/k['source']).read_bytes()==(HERE/'nonempty-replacement-kernels.lean').read_bytes()
checker['check_limits'](s['constructed_strict'])
print(json.dumps({'status':'PASS','public_pairs':2,'entries':len(read('nonempty-replacement-manifest.json')['entries']),'constructed_pairs':1,'physical_empty_only':True,'general_generated_empty_claim':False}))
