#!/usr/bin/env python3
import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
manifest = json.loads((HERE / 'literal-filter-manifest.json').read_text())
def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()
for entry in manifest['entries']:
    assert sha(ROOT / entry['path']) == entry['sha256'], entry['path']
for stem in manifest['selected_runs']:
    meta = json.loads((HERE / (stem + '.json')).read_text())
    assert meta['exit_code'] == 0, stem
    assert json.loads((HERE / meta['limits']).read_text()) == {
        'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}, stem
    if 'source' in meta:
        source = HERE / meta['source']
        assert sha(source) == meta['sha256'], stem
        assert meta['command'][-1] == str(source), stem
        assert '-Dlinter.all=true' in meta['command'], stem
for stem in ['literal-filter-direct-2', 'literal-filter-kernels-3']:
    assert not (HERE / (stem + '.log')).read_bytes(), stem
assert sha(ROOT / manifest['production']) == manifest['source_sha256']
assert sha(HERE / 'literal-filter-direct-2.source.lean') == manifest['source_sha256']
assert 'Build completed successfully (274 jobs).' in (HERE / 'literal-filter-canonical-1.log').read_text()
for stem, count, prints in [('literal-filter-public-1', 4, 4),
                             ('literal-filter-kernels-public-1', 1, 0)]:
    meta = json.loads((HERE / (stem + '.json')).read_text())
    source = (HERE / meta['source']).read_text()
    log = (HERE / meta['log']).read_text()
    for option in ['linter.all true', 'pp.explicit true', 'pp.fullNames true', 'pp.proofs true',
                   'pp.proofs.threshold 254', 'pp.universes true', 'pp.deepTerms true', 'pp.maxSteps 10000000']:
        assert 'set_option ' + option in source, (stem, option)
    assert len(re.findall(r'^#check @', source, re.M)) == count, stem
    assert len(re.findall(r'^#print (?!axioms )', source, re.M)) == prints, stem
    assert len(re.findall(r'^#print axioms ', source, re.M)) == count, stem
    assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|⋯|…|\.\.\.', log), stem
    reports = re.findall(r'depends on axioms:\s*\[([^\]]*)\]', log)
    assert len(reports) + len(re.findall('does not depend on any axioms', log)) == count, stem
    for report in reports:
        clean = re.sub(r'\.\{[^}]*\}', '', report)
        assert set(re.split(r',\s*', clean.strip())) <= {'propext', 'Classical.choice', 'Quot.sound'}, stem
print(json.dumps({'status': 'PASS', 'entries': len(manifest['entries']), 'public_pairs': 4,
                  'constructed_pairs': 1, 'strict_empty': True, 'canonical_jobs': 274,
                  'actual_memory_cap_bytes': 4294967296, 'actual_swap_cap_bytes': 0}))
