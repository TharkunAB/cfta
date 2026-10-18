import hashlib,json,importlib.util,subprocess,sys
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
manifest=json.loads((HERE/'query-source-kernels-manifest.json').read_text())
for item in manifest['entries']:
    path=ROOT/item['path']
    assert path.is_file() and path.stat().st_size==item['bytes'],path
    assert hashlib.sha256(path.read_bytes()).hexdigest()==item['sha256'],path
selection=json.loads((HERE/'query-source-kernels-selection.json').read_text())
assert selection['status']=='final'
assert selection['counts']=={'public_pairs':0,'constructed_pairs':2,'auxiliary_pairs':1}
spec=importlib.util.spec_from_file_location('checks',HERE/'query-source-probe-check.py')
checks=importlib.util.module_from_spec(spec);spec.loader.exec_module(checks)
for group in selection['selected_groups']:
    checks.check_group(group)
stem=selection['strict']
meta=json.loads((HERE/(stem+'.json')).read_text())
assert meta['exit_code']==0
assert (HERE/meta['log']).read_bytes()==b''
assert (HERE/meta['source']).read_bytes()==(HERE/'query-source-kernels.lean').read_bytes()
checks.check_limits(stem)
for stem in ['query-source-kernels-direct-1','query-source-kernels-public-1','query-source-claim-public-1']:
    meta=json.loads((HERE/(stem+'.json')).read_text())
    assert meta['sha256']==hashlib.sha256((HERE/meta['source']).read_bytes()).hexdigest()
subprocess.run([sys.executable,str(HERE/'used-mu-gap-verify.py')],check=True)
print(json.dumps({'status':'PASS','entries':len(manifest['entries']),**selection['counts'],'groups':2}))
