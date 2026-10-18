import hashlib,json,re,runpy
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
read=lambda n:json.loads((HERE/n).read_text())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for entry in read('outer-normal-manifest.json')['files']:
 path=ROOT/entry['path'];assert sha(path)==entry['sha256'],entry['path'];assert path.stat().st_size==entry['bytes']
v=runpy.run_path(str(HERE/'verify-probes.py'));s=read('outer-normal-selection.json');assert s['finalized']
for group in s['groups']:v['check_group'](group)
for stem,current in [(s['strict'],ROOT/'lean/MicroCFTA/SourceCurrentOuterUnionNormalHistory.lean'),(s['constructed_strict'],HERE/'outer-normal-kernels.lean')]:
 d=read(stem+'.json');assert d['exit_code']==0 and not(HERE/d['log']).read_bytes();assert sha(HERE/d['source'])==sha(current);v['check_limits'](stem)
d=read(s['canonical']+'.json');assert d['exit_code']==0
old=(ROOT/'lean/restart-evidence/20261018-native-renewal/full-audit-1.log').read_text()
assert re.findall(r'^warning:.*$',(HERE/d['log']).read_text(),re.M)==re.findall(r'^warning:.*$',old,re.M)
assert 'Build completed successfully' in (HERE/d['log']).read_text()
print(json.dumps(dict(status='PASS',pins=len(read('outer-normal-manifest.json')['files']),public_pairs=3,constructed_pairs=1,strict_zero_logs=2)))
