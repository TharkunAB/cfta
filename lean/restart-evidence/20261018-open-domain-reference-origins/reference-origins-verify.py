import hashlib,json,importlib.util
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
manifest=json.loads((HERE/'reference-origins-manifest.json').read_text())
for item in manifest['entries']:
    path=ROOT/item['path']
    assert path.is_file() and path.stat().st_size==item['bytes'],path
    assert hashlib.sha256(path.read_bytes()).hexdigest()==item['sha256'],path
selection=json.loads((HERE/'reference-origins-selection.json').read_text())
assert selection['status']=='final'
assert selection['counts']=={'public_pairs':5,'constructed_pairs':0,'auxiliary_pairs':0}
spec=importlib.util.spec_from_file_location('checks',HERE/'reference-origins-probe-check.py')
checks=importlib.util.module_from_spec(spec);spec.loader.exec_module(checks)
for group in selection['selected_groups']: checks.check_group(group)
strict=json.loads((HERE/(selection['strict']+'.json')).read_text())
assert strict['exit_code']==0
assert (HERE/strict['log']).read_bytes()==b''
source=ROOT/'lean/MicroCFTA/SourceCurrentNativeReferenceOrigins.lean'
assert (HERE/strict['source']).read_bytes()==source.read_bytes()
assert hashlib.sha256(source.read_bytes()).hexdigest()==selection['sha256']
canonical=json.loads((HERE/(selection['canonical']+'.json')).read_text())
assert canonical['exit_code']==0
assert 'Build completed successfully' in (HERE/canonical['log']).read_text()
for stem in ['reference-origins-direct-1','reference-origins-direct-2','reference-origins-direct-3','reference-origins-canonical-1','reference-origins-public-1']:
    checks.check_limits(stem)
    meta=json.loads((HERE/(stem+'.json')).read_text())
    if 'source' in meta:
        assert meta['sha256']==hashlib.sha256((HERE/meta['source']).read_bytes()).hexdigest()
assert json.loads((HERE/'reference-origins-direct-1.json').read_text())['exit_code']==1
assert json.loads((HERE/'reference-origins-direct-2.json').read_text())['exit_code']==0
assert (HERE/'reference-origins-direct-2.log').read_bytes()==b''
print(json.dumps({'status':'PASS','entries':len(manifest['entries']),**selection['counts'],'strict_log_bytes':0}))
