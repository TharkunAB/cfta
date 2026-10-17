#!/usr/bin/env python3
import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
manifest = json.loads((HERE/'publication-filter-manifest.json').read_text())

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def probe(stem,count):
    source=(HERE/(stem+'.source.lean')).read_text()
    log=(HERE/(stem+'.log')).read_text()
    for option in ['linter.all true','pp.explicit true','pp.fullNames true','pp.proofs true',
                   'pp.proofs.threshold 254','pp.universes true','pp.deepTerms true','pp.maxSteps 10000000']:
        assert 'set_option '+option in source,(stem,option)
    assert len(re.findall(r'^#check @',source,re.M))==count,stem
    assert len(re.findall(r'^#print (?!axioms )',source,re.M))==count,stem
    assert len(re.findall(r'^#print axioms ',source,re.M))==count,stem
    assert not re.search(r'(?i:failed to pretty print|pretty.?print[^\n]*(?:error|fail|exception)|uncaught exception|internal exception|maximum recursion depth|maximum number of heartbeats)|sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|pp\.rawOnError|⋯|…|\.\.\.',log),stem
    axioms=re.findall(r'depends on axioms:\s*\[([^\]]*)\]',log)
    assert len(axioms)+len(re.findall('does not depend on any axioms',log))==count,stem
    for used in axioms:
        used=re.sub(r'\.\{[^}]*\}','',used)
        assert set(re.split(r',\s*',used.strip())) <= {'propext','Classical.choice','Quot.sound'},used

for entry in manifest['entries']:
    assert sha(ROOT/entry['path'])==entry['sha256'],entry['path']
for production in manifest['productions']:
    assert sha(ROOT/production['path'])==production['sha256']
    assert sha(HERE/production['strict_snapshot'])==production['sha256']
for stem in manifest['selected_runs']:
    meta=json.loads((HERE/(stem+'.json')).read_text())
    assert meta['exit_code']==0,stem
    assert json.loads((HERE/meta['limits']).read_text())=={
        'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'},stem
    if 'source' in meta:
        source=HERE/meta['source']
        assert sha(source)==meta['sha256'],stem
        assert meta['command']==['/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean',
                                 '-Dlinter.all=true',str(source)],stem
for stem in ['publication-filter-direct-8','publication-filter-alignment-direct-3','publication-filter-kernels-2']:
    assert not (HERE/(stem+'.log')).read_bytes(),stem
for stem,count in [('publication-filter-source-canonical-1',608),('publication-filter-alignment-canonical-1',614)]:
    assert f'Build completed successfully ({count} jobs).' in (HERE/(stem+'.log')).read_text(),stem
probe('publication-filter-public-1',8)
probe('publication-filter-kernels-public-1',2)
for live,snapshot in [('publication-filter-public.lean','publication-filter-public-1.source.lean'),
                      ('publication-filter-kernels.lean','publication-filter-kernels-2.source.lean'),
                      ('publication-filter-kernels-public.lean','publication-filter-kernels-public-1.source.lean')]:
    assert sha(HERE/live)==sha(HERE/snapshot)
for meta_path in HERE.glob('publication-filter-*.json'):
    if meta_path.name.endswith('.limits.json') or meta_path.name=='publication-filter-manifest.json':
        continue
    meta=json.loads(meta_path.read_text())
    if 'command' in meta and 'source' in meta:
        assert sha(HERE/meta['source'])==meta['sha256'],meta_path.name
        assert (HERE/meta['log']).exists(),meta_path.name
first=json.loads((HERE/'publication-filter-direct-1.json').read_text())
assert first['exit_code']==1
assert 'Failed to connect to bus: Operation not permitted' in (HERE/first['log']).read_text()
assert not (HERE/first['limits']).exists()
assert json.loads((HERE/'publication-filter-kernels-1.json').read_text())['exit_code']==1
print(json.dumps(dict(status='PASS',entries=len(manifest['entries']),public_pairs=8,constructed_pairs=2,
    full_proof=True,strict_empty=True,productions=manifest['productions'],memory_max_high_bytes=4294967296,swap_max_bytes=0)))
