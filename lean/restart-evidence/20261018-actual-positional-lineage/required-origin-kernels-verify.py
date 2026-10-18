#!/usr/bin/env python3
import hashlib
import json
import re
from pathlib import Path
ROOT = Path('/home/tritlo/Code/mcfta')
HERE = Path(__file__).resolve().parent
manifest = json.loads((HERE/'required-origin-kernels-manifest.json').read_text())
for entry in manifest['entries']:
    data = (ROOT/entry['path']).read_bytes()
    assert len(data) == entry['bytes'], entry['path']
    assert hashlib.sha256(data).hexdigest() == entry['sha256'], entry['path']
limits = {'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
for metaPath in HERE.glob('required-origin-kernels-*.json'):
    meta = json.loads(metaPath.read_text())
    if 'exit_code' not in meta:
        continue
    assert json.loads((HERE/meta['limits']).read_text()) == limits, metaPath.name
    if 'source' in meta:
        source = HERE/meta['source']
        assert meta['command'] == ['/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean',
                                   '-Dlinter.all=true',str(source)], metaPath.name
        assert hashlib.sha256(source.read_bytes()).hexdigest() == meta['sha256'],metaPath.name
for stem in ['required-origin-kernels-3','required-origin-kernels-public-1']:
    assert json.loads((HERE/(stem+'.json')).read_text())['exit_code'] == 0, stem
assert (HERE/'required-origin-kernels-3.log').read_bytes() == b''
source = (HERE/'required-origin-kernels-public-1.source.lean').read_text()
output = (HERE/'required-origin-kernels-public-1.log').read_text()
for option in ['linter.all true','pp.explicit true','pp.fullNames true','pp.proofs true',
               'pp.proofs.threshold 254','pp.universes true','pp.deepTerms true','pp.maxSteps 10000000']:
    assert 'set_option '+option in source, option
heads = re.findall(r'^#check @([^\s]+)$',source,re.M)
assert heads == ['MicroCFTA.RequiredOriginKernels.positive_required_origin']
for head in heads:
    assert '#print '+head+'\n' in source
    assert '#print axioms '+head+'\n' in source
for bad in ['sorryAx','failed to pretty print','⋯','…','...','truncated','error:','warning:']:
    assert bad not in output, bad
reports = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",output)
assert len(reports) == 1 and reports[0][0] == heads[0]
for _,axioms in reports:
    names = {name.strip() for name in re.sub(r'\.\{[^}]*\}','',axioms).split(',') if name.strip()}
    assert names <= {'propext','Classical.choice','Quot.sound'}, names
production=ROOT/'lean/MicroCFTA/SourceCurrentActualRequiredRowOrigins.lean'
assert hashlib.sha256(production.read_bytes()).hexdigest()=='195ef26c2c787ed86771b6802bde817f5741295b4a475eadcc366c639c7d0e46'
for stem in ['required-origin-direct-5','required-origin-canonical-1']:
    meta=json.loads((HERE/(stem+'.json')).read_text())
    assert meta['exit_code']==0
    assert json.loads((HERE/meta['limits']).read_text())==limits
assert (HERE/'required-origin-direct-5.log').read_bytes()==b''
for attempt in [1,2]:
    assert json.loads((HERE/f'required-origin-kernels-{attempt}.json').read_text())['exit_code']!=0
print(json.dumps({'status':'PASS','entries':len(manifest['entries']),'public_pairs':0,
                  'constructed_pairs':1,'strict_empty':True,'actual_memory_cap_bytes':4294967296,
                  'actual_swap_cap_bytes':0}))
