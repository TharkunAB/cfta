#!/usr/bin/env python3
import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

manifest = json.loads((HERE / 'normalized-embedding-manifest.json').read_text())
for entry in manifest['entries']:
    assert sha(ROOT / entry['path']) == entry['sha256'], entry['path']
for stem in manifest['selected_runs']:
    meta = json.loads((HERE / (stem + '.json')).read_text())
    assert meta['exit_code'] == 0, stem
    limits = json.loads((HERE / meta['limits']).read_text())
    assert limits == {'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}, stem
    if 'source' in meta:
        source = HERE / meta['source']
        assert sha(source) == meta['sha256'], stem
        assert meta['command'][-1] == str(source), stem
        assert '-Dlinter.all=true' in meta['command'], stem
strict = json.loads((HERE / 'normalized-embedding-direct-4.json').read_text())
assert not (HERE / strict['log']).read_bytes()
assert sha(HERE / strict['source']) == manifest['source_sha256']
assert sha(ROOT / manifest['production']) == manifest['source_sha256']
canonical = (HERE / 'normalized-embedding-canonical-1.log').read_text()
assert 'Build completed successfully (116 jobs).' in canonical
meta = json.loads((HERE / 'normalized-embedding-public-1.json').read_text())
source = (HERE / meta['source']).read_text()
log = (HERE / meta['log']).read_text()
for option in ['linter.all true', 'pp.explicit true', 'pp.fullNames true', 'pp.proofs true',
               'pp.proofs.threshold 254', 'pp.universes true', 'pp.deepTerms true', 'pp.maxSteps 10000000']:
    assert 'set_option ' + option in source, option
assert len(re.findall(r'^#check @', source, re.M)) == 3
assert len(re.findall(r'^#print (?!axioms )', source, re.M)) == 3
assert len(re.findall(r'^#print axioms ', source, re.M)) == 3
assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|⋯|…|\.\.\.', log)
reports = re.findall(r'depends on axioms:\s*\[([^\]]*)\]', log)
assert len(reports) + len(re.findall('does not depend on any axioms', log)) == 3
for report in reports:
    clean = re.sub(r'\.\{[^}]*\}', '', report)
    assert set(re.split(r',\s*', clean.strip())) <= {'propext', 'Classical.choice', 'Quot.sound'}
print(json.dumps({'status': 'PASS', 'entries': len(manifest['entries']), 'public_pairs': 3, 'constructed_pairs': 0,
                  'strict_empty': True, 'canonical_jobs': 116, 'actual_memory_cap_bytes': 4294967296, 'actual_swap_cap_bytes': 0}))
