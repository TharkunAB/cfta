#!/usr/bin/env python3
import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
manifest = json.loads((HERE / 'independent-union-review-manifest.json').read_text())
def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()
for entry in manifest['entries']:
    assert sha(ROOT / entry['path']) == entry['sha256'], entry['path']
for name, expected in manifest['production_hashes'].items():
    assert sha(ROOT / 'lean/MicroCFTA' / (name + '.lean')) == expected, name
for stem in manifest['selected_runs']:
    meta = json.loads((HERE / (stem + '.json')).read_text())
    assert meta['exit_code'] == 0, stem
    assert json.loads((HERE / meta['limits']).read_text()) == {
        'memory.max':'4294967296', 'memory.high':'4294967296', 'memory.swap.max':'0'}, stem
    if 'source' in meta:
        source = HERE / meta['source']
        assert sha(source) == meta['sha256'], stem
        assert meta['command'][-1] == str(source), stem
        assert '-Dlinter.all=true' in meta['command'], stem
for stem in ['paired-union-direct-7', 'live-union-direct-2',
             'paired-union-kernels-1', 'live-union-kernels-2']:
    assert not (HERE / (stem + '.log')).read_bytes(), stem
for stem, jobs in [('paired-union-canonical-1',599),('live-union-canonical-1',602)]:
    log = (HERE / (stem + '.log')).read_text()
    assert f'Build completed successfully ({jobs} jobs).' in log, stem
    assert not re.search(r'warning:|error:|failed to pretty print',log), stem
for stem,count in [('paired-union-public-1',6),('live-union-public-1',3),
                   ('paired-union-kernels-public-1',2),('live-union-kernels-public-1',1)]:
    source = (HERE / (stem + '.source.lean')).read_text()
    log = (HERE / (stem + '.log')).read_text()
    for option in ['linter.all true','pp.explicit true','pp.fullNames true','pp.proofs true',
                   'pp.proofs.threshold 254','pp.universes true','pp.deepTerms true','pp.maxSteps 10000000']:
        assert 'set_option '+option in source,(stem,option)
    assert len(re.findall(r'^#check @',source,re.M)) == count,stem
    assert len(re.findall(r'^#print (?!axioms )',source,re.M)) == count,stem
    assert len(re.findall(r'^#print axioms ',source,re.M)) == count,stem
    assert not re.search(r'(?i:failed to pretty print|pretty.?print[^\n]*(?:error|fail|exception)|uncaught exception|internal exception|maximum recursion depth)|sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|⋯|…|\.\.\.',log),stem
    reports = re.findall(r'depends on axioms:\s*\[([^\]]*)\]',log)
    assert len(reports)+len(re.findall('does not depend on any axioms',log)) == count,stem
    for report in reports:
        clean = re.sub(r'\.\{[^}]*\}','',report)
        assert set(re.split(r',\s*',clean.strip())) <= {'propext','Classical.choice','Quot.sound'},stem
for prefix,number in [('paired-union-kernels',1),('live-union-kernels',2)]:
    assert (HERE / (prefix+'-public-1.source.lean')).read_bytes().startswith(
        (HERE / (prefix+f'-{number}.source.lean')).read_bytes()),prefix
print(json.dumps({'status':'PASS','entries':len(manifest['entries']),
                  'existing_public_pairs_reviewed':9,'existing_constructed_pairs_reviewed':3,
                  'new_pairs':0,'builds_repeated':0}))
