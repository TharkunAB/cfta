#!/usr/bin/env python3
import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
manifest = json.loads((HERE / 'dependency-descent-manifest.json').read_text())
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
for stem in ['dependency-descent-direct-2', 'dependency-descent-kernels-6']:
    assert not (HERE / (stem + '.log')).read_bytes(), stem
assert sha(ROOT / manifest['production']) == manifest['source_sha256']
assert sha(HERE / 'dependency-descent-direct-2.source.lean') == manifest['source_sha256']
assert 'Build completed successfully (987 jobs).' in (HERE / 'dependency-descent-canonical-1.log').read_text()
for stem, count, prints in [('dependency-descent-public-1', 2, 2),
                             ('dependency-descent-kernels-public-2', 2, 0)]:
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
assert sha(HERE / 'dependency-descent-kernels.lean') == sha(HERE / 'dependency-descent-kernels-6.source.lean')
for index in range(1, 5):
    assert json.loads((HERE / f'dependency-descent-kernels-{index}.json').read_text())['exit_code'] == 1
assert 'warning:' in (HERE / 'dependency-descent-kernels-5.log').read_text()
assert 'warning:' in (HERE / 'dependency-descent-kernels-public-1.log').read_text()
print(json.dumps({'status': 'PASS', 'entries': len(manifest['entries']), 'public_pairs': 2,
                  'constructed_pairs': 2, 'strict_empty': True, 'canonical_jobs': 987,
                  'actual_memory_cap_bytes': 4294967296, 'actual_swap_cap_bytes': 0}))
