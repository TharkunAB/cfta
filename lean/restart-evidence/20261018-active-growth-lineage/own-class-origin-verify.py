#!/usr/bin/env python3
"""Check the frozen own-class-origin proof evidence without running Lean."""
import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
manifest = json.loads((HERE / 'own-class-origin-manifest.json').read_text())


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


for entry in manifest['entries']:
    path = ROOT / entry['path']
    assert path.stat().st_size == entry['bytes'], entry['path']
    assert sha(path) == entry['sha256'], entry['path']
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
for stem in ['own-class-origin-direct-5', 'own-class-origin-kernels-1']:
    assert not (HERE / (stem + '.log')).read_bytes(), stem
assert sha(ROOT / manifest['production']) == manifest['source_sha256']
assert sha(HERE / 'own-class-origin-direct-5.source.lean') == manifest['source_sha256']
canonical = (HERE / 'own-class-origin-canonical-1.log').read_text()
assert 'Build completed successfully (1348 jobs).' in canonical
assert len(re.findall(r'^warning:', canonical, re.M)) == 1
assert 'InternedFreshOrdinaryClosedCompletion.lean:24:5' in canonical
assert 'error:' not in canonical
for stem, count in [('own-class-origin-public-1', 3), ('own-class-origin-kernels-public-1', 1)]:
    meta = json.loads((HERE / (stem + '.json')).read_text())
    source = (HERE / meta['source']).read_text()
    log = (HERE / meta['log']).read_text()
    for option in ['linter.all true', 'pp.explicit true', 'pp.fullNames true', 'pp.proofs true',
                   'pp.proofs.threshold 254', 'pp.universes true', 'pp.deepTerms true', 'pp.maxSteps 10000000']:
        assert 'set_option ' + option in source, (stem, option)
    assert len(re.findall(r'^#check @', source, re.M)) == count, stem
    assert len(re.findall(r'^#print (?!axioms )', source, re.M)) == count, stem
    assert len(re.findall(r'^#print axioms ', source, re.M)) == count, stem
    assert not re.search(r'(?i:failed to pretty print|pretty.?print[^\n]*(?:error|fail|exception)|uncaught exception|internal exception|maximum recursion depth|truncated)|sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|⋯|…|\.\.\.', log), stem
    reports = re.findall(r'depends on axioms:\s*\[([^\]]*)\]', log)
    assert len(reports) + len(re.findall('does not depend on any axioms', log)) == count, stem
    for report in reports:
        clean = re.sub(r'\.\{[^}]*\}', '', report)
        assert set(re.split(r',\s*', clean.strip())) <= {'propext', 'Classical.choice', 'Quot.sound'}, stem
fixture = HERE / 'own-class-origin-kernels-1.source.lean'
assert sha(HERE / 'own-class-origin-kernels.lean') == sha(fixture)
assert (HERE / 'own-class-origin-kernels-public-1.source.lean').read_bytes().startswith(fixture.read_bytes())
for attempt in [1, 2, 3]:
    failed = json.loads((HERE / f'own-class-origin-direct-{attempt}.json').read_text())
    assert failed['exit_code'] == 1
    source = HERE / failed['source']
    assert failed['command'][-1] == str(source)
    assert sha(source) == failed['sha256']
for meta_path in HERE.glob('own-class-origin-*.json'):
    if meta_path.name.endswith(('.limits.json', '-manifest.json')):
        continue
    meta = json.loads(meta_path.read_text())
    if 'limits' not in meta:
        continue
    assert json.loads((HERE / meta['limits']).read_text()) == {
        'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}
print(json.dumps({'status': 'PASS', 'entries': len(manifest['entries']), 'public_pairs': 3,
                  'constructed_pairs': 1, 'strict_empty': True, 'canonical_jobs': 1348,
                  'old_dependency_warnings': 1, 'actual_memory_cap_bytes': 4294967296,
                  'actual_swap_cap_bytes': 0}))
