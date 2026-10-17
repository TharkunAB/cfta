#!/usr/bin/env python3
import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
manifest = json.loads((HERE / 'class-selected-kernels-manifest.json').read_text())


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


for entry in manifest['entries']:
    assert sha(ROOT / entry['path']) == entry['sha256'], entry['path']
for stem in manifest['selected_runs']:
    meta = json.loads((HERE / (stem + '.json')).read_text())
    assert meta['exit_code'] == 0, stem
    assert json.loads((HERE / meta['limits']).read_text()) == {
        'memory.max': '4294967296', 'memory.high': '4294967296',
        'memory.swap.max': '0'}, stem
    if 'source' in meta:
        source = HERE / meta['source']
        assert sha(source) == meta['sha256'], stem
        assert meta['command'] == [
            '/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean',
            '-Dlinter.all=true', str(source)], stem
assert sha(ROOT / manifest['reviewed_production']) == manifest['source_sha256']
assert sha(HERE / 'class-selected-direct-7.source.lean') == manifest['source_sha256']
for stem in ['class-selected-direct-7', 'class-selected-kernels-2']:
    assert not (HERE / (stem + '.log')).read_bytes(), stem
assert 'Build completed successfully (1417 jobs).' in (HERE / 'class-selected-canonical-1.log').read_text()
assert sha(HERE / 'class-selected-kernels.lean') == sha(HERE / 'class-selected-kernels-2.source.lean')
assert sha(HERE / 'class-selected-kernels-public.lean') == sha(HERE / 'class-selected-kernels-public-1.source.lean')
for stem in ['class-selected-kernels-2', 'class-selected-kernels-public-1']:
    source = (HERE / (stem + '.source.lean')).read_text()
    for option in [
        'linter.all true', 'pp.explicit true', 'pp.fullNames true',
        'pp.proofs true', 'pp.proofs.threshold 254', 'pp.universes true',
        'pp.deepTerms true', 'pp.maxSteps 10000000',
    ]:
        assert 'set_option ' + option in source, (stem, option)
source = (HERE / 'class-selected-kernels-public-1.source.lean').read_text()
log = (HERE / 'class-selected-kernels-public-1.log').read_text()
assert len(re.findall(r'^#check @', source, re.M)) == 1
assert len(re.findall(r'^#print (?!axioms )', source, re.M)) == 1
assert len(re.findall(r'^#print axioms ', source, re.M)) == 1
assert not re.search(
    r'(?i:failed to pretty print|pretty.?print[^\n]*(?:error|fail|exception)|'
    r'uncaught exception|internal exception|maximum recursion depth|maximum number of heartbeats)'
    r'|sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|pp\.rawOnError|⋯|…|\.\.\.', log)
reports = re.findall(r'depends on axioms:\s*\[([^\]]*)\]', log)
assert len(reports) + len(re.findall('does not depend on any axioms', log)) == 1
for report in reports:
    clean = re.sub(r'\.\{[^}]*\}', '', report)
    assert set(re.split(r',\s*', clean.strip())) <= {'propext', 'Classical.choice', 'Quot.sound'}
for attempt, expected in [(1,1),(2,0)]:
    meta = json.loads((HERE / ('class-selected-kernels-' + str(attempt) + '.json')).read_text())
    assert meta['exit_code'] == expected
    assert sha(HERE / meta['source']) == meta['sha256']
    assert json.loads((HERE / meta['limits']).read_text()) == {
        'memory.max':'4294967296', 'memory.high':'4294967296',
        'memory.swap.max':'0'}
print(json.dumps({
    'status': 'PASS', 'entries': len(manifest['entries']),
    'constructed_pairs': 1, 'full_proof': True, 'strict_empty': True,
    'reviewed_source_sha256': manifest['source_sha256'],
    'actual_memory_max_high_bytes': 4294967296, 'actual_swap_max_bytes': 0,
}))
