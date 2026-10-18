import hashlib,json,re,runpy
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
prefix='issued-writers'
read=lambda name:json.loads((HERE/name).read_text())
sha=lambda path:hashlib.sha256(path.read_bytes()).hexdigest()
for item in read(prefix+'-manifest.json')['entries']:
 assert sha(ROOT/item['path'])==item['sha256'],item['path']
s=read(prefix+'-selection.json')
c=runpy.run_path(str(HERE/'verify-probes.py'))
for group in s['groups']:c['check_group'](group)
for stem in [s['strict'],s['constructed_strict']]:
 r=read(stem+'.json');assert r['exit_code']==0 and not (HERE/r['log']).read_bytes();c['check_limits'](stem)
r=read(s['strict']+'.json');assert (ROOT/'lean/MicroCFTA'/(s['module']+'.lean')).read_bytes()==(HERE/r['source']).read_bytes()
r=read(s['constructed_strict']+'.json');assert (HERE/(prefix+'-kernels.lean')).read_bytes()==(HERE/r['source']).read_bytes()
r=read(s['canonical']+'.json');log=(HERE/r['log']).read_text();assert r['exit_code']==0 and 'Build completed successfully' in log
assert not re.search(r'warning:|error:',log);c['check_limits'](s['canonical'])
print(json.dumps({'status':'PASS','public_pairs':sum(g['pairs'] for g in s['groups'] if g['kind']=='new-public'),'constructed_pairs':1,'pins':len(read(prefix+'-manifest.json')['entries'])}))
