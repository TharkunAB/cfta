#!/usr/bin/env python3
import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
manifest = json.loads((HERE/'binder-result-manifest.json').read_text())


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def options(source):
    for option in ['linter.all true','pp.explicit true','pp.fullNames true',
                   'pp.proofs true','pp.proofs.threshold 254','pp.universes true',
                   'pp.deepTerms true','pp.maxSteps 10000000']:
        assert 'set_option '+option in source, option


def probe(stem, count):
    source=(HERE/(stem+'.source.lean')).read_text()
    log=(HERE/(stem+'.log')).read_text()
    options(source)
    assert len(re.findall(r'^#check @',source,re.M))==count
    assert len(re.findall(r'^#print (?!axioms )',source,re.M))==count
    assert len(re.findall(r'^#print axioms ',source,re.M))==count
    assert not re.search(r'(?i:failed to pretty print|pretty.?print[^\n]*(?:error|fail|exception)|uncaught exception|internal exception|maximum recursion depth|maximum number of heartbeats)|sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|pp\.rawOnError|⋯|…|\.\.\.',log)
    axioms=re.findall(r'depends on axioms:\s*\[([^\]]*)\]',log)
    assert len(axioms)+len(re.findall('does not depend on any axioms',log))==count
    for used in axioms:
        used=re.sub(r'\.\{[^}]*\}','',used)
        assert set(re.split(r',\s*',used.strip())) <= {'propext','Classical.choice','Quot.sound'}


for entry in manifest['entries']:
    assert sha(ROOT/entry['path'])==entry['sha256'],entry['path']
for stem in manifest['selected_runs']:
    meta=json.loads((HERE/(stem+'.json')).read_text())
    assert meta['exit_code']==0,stem
    assert json.loads((HERE/meta['limits']).read_text())=={
        'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'},stem
    if 'source' in meta:
        source=HERE/meta['source']
        assert sha(source)==meta['sha256'],stem
        assert meta['command']==['/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean','-Dlinter.all=true',str(source)],stem
assert sha(ROOT/manifest['production'])==manifest['source_sha256']
assert sha(HERE/'binder-result-direct-4.source.lean')==manifest['source_sha256']
for stem in ['binder-result-direct-4','binder-result-kernels-3']:
    assert not (HERE/(stem+'.log')).read_bytes(),stem
assert 'Build completed successfully (603 jobs).' in (HERE/'binder-result-canonical-2.log').read_text()
probe('binder-result-public-1',2)
probe('binder-result-kernels-public-1',1)
for live,snapshot in [('binder-result-public.lean','binder-result-public-1.source.lean'),
                      ('binder-result-kernels.lean','binder-result-kernels-3.source.lean'),
                      ('binder-result-kernels-public.lean','binder-result-kernels-public-1.source.lean')]:
    assert sha(HERE/live)==sha(HERE/snapshot)
for stem,code in [('binder-result-direct-1',1),('binder-result-direct-2',0),
                  ('binder-result-direct-3',1),('binder-result-kernels-1',1),('binder-result-kernels-2',1)]:
    meta=json.loads((HERE/(stem+'.json')).read_text())
    assert meta['exit_code']==code
    assert sha(HERE/meta['source'])==meta['sha256']
    assert json.loads((HERE/meta['limits']).read_text())=={
        'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
print(json.dumps(dict(status='PASS',entries=len(manifest['entries']),public_pairs=2,
    constructed_pairs=1,full_proof=True,strict_empty=True,source_sha256=manifest['source_sha256'],
    memory_max_high_bytes=4294967296,swap_max_bytes=0)))
