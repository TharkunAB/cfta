import hashlib,json,runpy
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
checks=runpy.run_path(str(HERE/'verify-probes.py'))
manifest=json.loads((HERE/'root-physical-manifest.json').read_text())
for item in manifest['entries']:
    path=ROOT/item['path'];data=path.read_bytes()
    assert hashlib.sha256(data).hexdigest()==item['sha256'] and len(data)==item['bytes'],item['path']
stricts={'SourceCurrentMuReconstructionEffects':'mu-effects-direct-1','SourceCurrentLowerProbeHeap':'lower-probes-direct-2','SourceCurrentParentProbeHeap':'parent-probes-direct-1'}
for name,stem in stricts.items():
    meta=json.loads((HERE/(stem+'.json')).read_text())
    assert meta['exit_code']==0 and (HERE/meta['log']).read_bytes()==b''
    assert (HERE/meta['source']).read_bytes()==(ROOT/'lean/MicroCFTA'/f'{name}.lean').read_bytes()
    assert meta['command']==['/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean','-Dlinter.all=true',str(HERE/meta['source'])]
    checks['check_limits'](stem)
for stem in ['mu-effects-kernels-2','parent-probes-kernels-1']:
    meta=json.loads((HERE/(stem+'.json')).read_text())
    assert meta['exit_code']==0 and (HERE/meta['log']).read_bytes()==b''
    checks['check_limits'](stem)
for stem in ['mu-effects-canonical-1','lower-probes-canonical-1','parent-probes-canonical-1']:
    meta=json.loads((HERE/(stem+'.json')).read_text())
    assert meta['exit_code']==0 and 'Build completed successfully' in (HERE/meta['log']).read_text()
    checks['check_limits'](stem)
for stem,count,kind in [('mu-effects-public-1',4,'new-public'),('lower-probes-public-1',17,'new-public'),('parent-probes-public-1',7,'new-public'),('mu-effects-kernels-public-1',2,'constructed'),('parent-probes-kernels-public-1',2,'constructed')]:
    checks['check_group']({'name':stem,'pairs':count,'kind':kind,'full_proof':True})
print(json.dumps({'status':'PASS','entries':len(manifest['entries']),'public_pairs':28,'constructed_pairs':4,'strict_production_logs_empty':3,'strict_constructed_logs_empty':2,'memory_max':4294967296,'memory_high':4294967296,'swap_max':0}))
