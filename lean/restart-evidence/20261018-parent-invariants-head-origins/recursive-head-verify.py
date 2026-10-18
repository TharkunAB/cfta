#!/usr/bin/env python3
"""Verify the frozen recursive Head row-origin evidence without running Lean."""
import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
manifest = json.loads((HERE / 'recursive-head-manifest.json').read_text())


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


for entry in manifest['entries']:
    path = ROOT / entry['path']
    assert path.stat().st_size == entry['bytes'], entry['path']
    assert sha(path) == entry['sha256'], entry['path']
limits = {'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}
for path in HERE.glob('recursive-head-*.json'):
    meta = json.loads(path.read_text())
    if 'command' not in meta:
        continue
    assert json.loads((HERE / meta['limits']).read_text()) == limits, path.name
    if 'source' in meta:
        source = HERE / meta['source']
        assert sha(source) == meta['sha256'], path.name
        assert meta['command'][-1] == str(source), path.name
        assert '-Dlinter.all=true' in meta['command'], path.name
for stem in manifest['selected_runs']:
    assert json.loads((HERE / (stem + '.json')).read_text())['exit_code'] == 0, stem
for stem in ['recursive-head-direct-4', 'recursive-head-kernels-4']:
    assert (HERE / (stem + '.log')).stat().st_size == 0, stem
assert sha(ROOT / manifest['production']) == manifest['source_sha256']
assert sha(HERE / 'recursive-head-direct-4.source.lean') == manifest['source_sha256']
canonical = (HERE / 'recursive-head-canonical-1.log').read_text()
assert 'Build completed successfully (1424 jobs).' in canonical
assert len(re.findall(r'^warning:', canonical, re.M)) == 1
assert 'InternedFreshOrdinaryClosedCompletion.lean:24:5' in canonical
assert 'error:' not in canonical
for stem, count in [('recursive-head-public-1', 6), ('recursive-head-kernels-public-1', 2)]:
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
fixture = HERE / 'recursive-head-kernels-4.source.lean'
assert sha(HERE / 'recursive-head-kernels.lean') == sha(fixture)
assert (HERE / 'recursive-head-kernels-public-1.source.lean').read_bytes().startswith(fixture.read_bytes())
for attempt in [1, 2, 3]:
    assert json.loads((HERE / f'recursive-head-direct-{attempt}.json').read_text())['exit_code'] == 1
    assert json.loads((HERE / f'recursive-head-kernels-{attempt}.json').read_text())['exit_code'] == 1
print(json.dumps({'status': 'PASS', 'entries': len(manifest['entries']), 'public_pairs': 6,
                  'constructed_pairs': 2, 'strict_empty': True, 'canonical_jobs': 1424,
                  'old_dependency_warnings': 1, 'actual_memory_cap_bytes': 4294967296,
                  'actual_swap_cap_bytes': 0}))
