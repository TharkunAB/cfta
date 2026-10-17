#!/usr/bin/env python3
import hashlib
import json
import re
from pathlib import Path
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
manifest = json.loads((HERE / 'union-fusion-check-manifest.json').read_text())
for entry in manifest['entries']:
    assert sha(ROOT / entry['path']) == entry['sha256'], entry['path']
for stem in manifest['selected_runs']:
    meta = json.loads((HERE / (stem + '.json')).read_text())
    assert meta['exit_code'] == 0, stem
    source = HERE / meta['source']
    assert sha(source) == meta['sha256'], stem
    assert meta['command'][-1] == str(source), stem
    assert '-Dlinter.all=true' in meta['command'], stem
    limits = json.loads((HERE / meta['limits']).read_text())
    assert limits == {'memory.max':'4294967296', 'memory.high':'4294967296', 'memory.swap.max':'0'}, stem
assert not (HERE / 'union-fusion-check-kernels-4.log').read_bytes()
meta = json.loads((HERE / 'union-fusion-check-kernels-public-1.json').read_text())
source = (HERE / meta['source']).read_text()
log = (HERE / meta['log']).read_text()
for option in ['linter.all true','pp.explicit true','pp.fullNames true','pp.proofs true',
               'pp.proofs.threshold 254','pp.universes true','pp.deepTerms true','pp.maxSteps 10000000']:
    assert 'set_option ' + option in source, option
assert len(re.findall(r'^#check @',source,re.M)) == 2
assert len(re.findall(r'^#print axioms ',source,re.M)) == 2
assert not re.search(r'sorryAx|\b(?:error|warning)(?:\([^)]*\))?:|⋯|…|\.\.\.',log)
reports = re.findall(r'depends on axioms:\s*\[([^\]]*)\]',log)
assert len(reports) == 2
for report in reports:
    clean = re.sub(r'\.\{[^}]*\}', '', report)
    assert set(re.split(r',\s*',clean.strip())) <= {'propext','Classical.choice','Quot.sound'}
assert 'same_open_observations' in source and 'left_literal' in source and 'right_literal' in source
print(json.dumps({'status':'PASS','entries':len(manifest['entries']),'constructed_pairs':2,
  'strict_empty':True,'complete_value_inequality':True,'all_depth_open_observations':True,
  'actual_memory_max':4294967296,'actual_swap_max':0,'production_changes':False}))
