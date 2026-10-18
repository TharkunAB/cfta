import hashlib,json,runpy
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
def read(name): return json.loads((HERE/name).read_text())
for e in read('lexical-manifest.json')['entries']:
 p=ROOT/e['path']; assert hashlib.sha256(p.read_bytes()).hexdigest()==e['sha256'],e['path']
s=read('lexical-selection.json')
assert read(s['strict']+'.json')['exit_code']==0
assert not (HERE/(s['strict']+'.log')).read_bytes()
assert (HERE/(s['strict']+'.source.lean')).read_bytes()==(ROOT/'lean/MicroCFTA/SourceCurrentGeneratedLexicalCases.lean').read_bytes()
c=read(s['canonical']+'.json'); assert c['exit_code']==0
l=(HERE/c['log']).read_text(); assert 'Build completed successfully' in l and 'warning:' not in l
checker=runpy.run_path(str(HERE/'verify-probes.py'))
checker['check_limits'](s['strict']);checker['check_limits'](s['canonical'])
for g in s['groups']: checker['check_group'](g)
print(json.dumps({'status':'PASS','public_pairs':2,'entries':len(read('lexical-manifest.json')['entries']),'root_filter_claim':False,'semantic_observation_claim':False}))
