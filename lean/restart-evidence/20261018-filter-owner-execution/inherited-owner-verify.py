#!/usr/bin/env python3
"""Check the frozen inherited-owner proof evidence without running Lean."""
import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
manifest = json.loads((HERE / 'inherited-owner-manifest.json').read_text())


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
for stem in ['inherited-owner-direct-2', 'inherited-owner-kernels-4']:
    assert not (HERE / (stem + '.log')).read_bytes(), stem
assert sha(ROOT / manifest['production']) == manifest['source_sha256']
assert sha(HERE / 'inherited-owner-direct-2.source.lean') == manifest['source_sha256']
canonical = (HERE / 'inherited-owner-canonical-1.log').read_text()
assert 'Build completed successfully (1331 jobs).' in canonical
assert len(re.findall(r'^warning:', canonical, re.M)) == 1
assert 'InternedFreshOrdinaryClosedCompletion.lean:24:5' in canonical
assert 'error:' not in canonical
for stem in ['inherited-owner-public-1', 'inherited-owner-kernels-public-2']:
    meta = json.loads((HERE / (stem + '.json')).read_text())
    source = (HERE / meta['source']).read_text()
    log = (HERE / meta['log']).read_text()
    for option in ['linter.all true', 'pp.explicit true', 'pp.fullNames true', 'pp.proofs true',
                   'pp.proofs.threshold 254', 'pp.universes true', 'pp.deepTerms true', 'pp.maxSteps 10000000']:
        assert 'set_option ' + option in source, (stem, option)
    assert len(re.findall(r'^#check @', source, re.M)) == 2, stem
    assert len(re.findall(r'^#print (?!axioms )', source, re.M)) == 2, stem
    assert len(re.findall(r'^#print axioms ', source, re.M)) == 2, stem
    assert not re.search(r'(?i:failed to pretty print|pretty.?print[^\n]*(?:error|fail|exception)|uncaught exception|internal exception|maximum recursion depth|truncated)|sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|⋯|…|\.\.\.', log), stem
    reports = re.findall(r'depends on axioms:\s*\[([^\]]*)\]', log)
    assert len(reports) + len(re.findall('does not depend on any axioms', log)) == 2, stem
    for report in reports:
        clean = re.sub(r'\.\{[^}]*\}', '', report)
        assert set(re.split(r',\s*', clean.strip())) <= {'propext', 'Classical.choice', 'Quot.sound'}, stem
fixture = HERE / 'inherited-owner-kernels-4.source.lean'
assert sha(HERE / 'inherited-owner-kernels.lean') == sha(fixture)
assert (HERE / 'inherited-owner-kernels-public-2.source.lean').read_bytes().startswith(fixture.read_bytes())
failed = json.loads((HERE / 'inherited-owner-kernels-public-1.json').read_text())
assert failed['exit_code'] == -15
assert failed['log'] != 'inherited-owner-kernels-public-2.log'
print(json.dumps({'status': 'PASS', 'entries': len(manifest['entries']), 'public_pairs': 2,
                  'constructed_pairs': 2, 'strict_empty': True, 'canonical_jobs': 1331,
                  'old_dependency_warnings': 1, 'actual_memory_cap_bytes': 4294967296,
                  'actual_swap_cap_bytes': 0}))
