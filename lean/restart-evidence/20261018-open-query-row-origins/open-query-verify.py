import hashlib,json,importlib.util
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
m=json.loads((HERE/'open-query-manifest.json').read_text())
for item in m['entries']:
    p=ROOT/item['path']
    assert p.is_file() and p.stat().st_size==item['bytes'],p
    assert hashlib.sha256(p.read_bytes()).hexdigest()==item['sha256'],p
selection=json.loads((HERE/'open-query-selection.json').read_text())
assert selection['status']=='final'
assert selection['counts']=={'public_pairs':4,'constructed_pairs':0,'auxiliary_pairs':0}
spec=importlib.util.spec_from_file_location('checks',HERE/'open-query-probe-check.py')
checks=importlib.util.module_from_spec(spec);spec.loader.exec_module(checks)
for group in selection['selected_groups']: checks.check_group(group)
strict=json.loads((HERE/(selection['strict']+'.json')).read_text())
assert strict['exit_code']==0 and (HERE/strict['log']).read_bytes()==b''
source=ROOT/'lean/MicroCFTA/SourceCurrentNativeOpenQueryRowOrigins.lean'
assert source.read_bytes()==(HERE/strict['source']).read_bytes()
assert hashlib.sha256(source.read_bytes()).hexdigest()==selection['sha256']
canonical=json.loads((HERE/(selection['canonical']+'.json')).read_text())
assert canonical['exit_code']==0 and 'Build completed successfully' in (HERE/canonical['log']).read_text()
for stem in [selection['strict'],selection['canonical'],selection['public_group']]:
    checks.check_limits(stem)
    meta=json.loads((HERE/(stem+'.json')).read_text())
    if 'source' in meta: assert meta['sha256']==hashlib.sha256((HERE/meta['source']).read_bytes()).hexdigest()
for stem in ['open-query-direct-1','open-query-direct-2']:
    checks.check_limits(stem)
    meta=json.loads((HERE/(stem+'.json')).read_text())
    assert meta['exit_code']==1
    assert meta['sha256']==hashlib.sha256((HERE/meta['source']).read_bytes()).hexdigest()
print(json.dumps({'status':'PASS','entries':len(m['entries']),**selection['counts'],'strict_log_bytes':0}))
