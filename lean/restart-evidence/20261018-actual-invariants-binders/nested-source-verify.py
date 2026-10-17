#!/usr/bin/env python3
import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def probe(stem, count):
    source = (HERE / (stem + '.source.lean')).read_text()
    log = (HERE / (stem + '.log')).read_text()
    for option in ['linter.all true', 'pp.explicit true', 'pp.fullNames true',
                   'pp.proofs true', 'pp.proofs.threshold 254', 'pp.universes true',
                   'pp.deepTerms true', 'pp.maxSteps 10000000']:
        assert 'set_option ' + option in source, (stem, option)
    assert len(re.findall(r'^#check @', source, re.M)) == count, stem
    assert len(re.findall(r'^#print (?!axioms )', source, re.M)) == count, stem
    assert len(re.findall(r'^#print axioms ', source, re.M)) == count, stem
    assert not re.search(r'(?i:failed to pretty print|pretty.?print[^\n]*(?:error|fail|exception)|uncaught exception|internal exception|maximum recursion depth|maximum number of heartbeats)|sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|pp\.rawOnError|⋯|…|\.\.\.', log), stem
    axioms = re.findall(r'depends on axioms:\s*\[([^\]]*)\]', log)
    assert len(axioms) + len(re.findall('does not depend on any axioms', log)) == count, stem
    for used in axioms:
        used = re.sub(r'\.\{[^}]*\}', '', used)
        assert set(re.split(r',\s*', used.strip())) <= {'propext', 'Classical.choice', 'Quot.sound'}, used


manifest = json.loads((HERE / 'nested-source-manifest.json').read_text())
for entry in manifest['entries']:
    assert sha(ROOT / entry['path']) == entry['sha256'], entry['path']
for production in manifest['productions']:
    assert sha(ROOT / production['path']) == production['sha256']
    assert sha(HERE / production['strict_snapshot']) == production['sha256']
for stem in manifest['selected_runs']:
    meta = json.loads((HERE / (stem + '.json')).read_text())
    assert meta['exit_code'] == 0, stem
    assert json.loads((HERE / meta['limits']).read_text()) == {
        'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}, stem
    if 'source' in meta:
        source = HERE / meta['source']
        assert sha(source) == meta['sha256'], stem
        assert meta['command'] == [
            '/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean',
            '-Dlinter.all=true', str(source)], stem
for stem in ['nested-source-direct-4', 'nested-source-kernels-3']:
    assert (HERE / (stem + '.log')).stat().st_size == 0, stem
canonical = (HERE / 'nested-source-canonical-1.log').read_text()
assert 'Build completed successfully (583 jobs).' in canonical
assert not re.search(r'\b(?:warning|error):', canonical)
probe('nested-source-public-1', 5)
probe('nested-source-kernels-public-1', 2)
for live, snapshot in [
    ('nested-source-public.lean', 'nested-source-public-1.source.lean'),
    ('nested-source-kernels.lean', 'nested-source-kernels-3.source.lean'),
    ('nested-source-kernels-public.lean', 'nested-source-kernels-public-1.source.lean')]:
    assert sha(HERE / live) == sha(HERE / snapshot)
for path in HERE.glob('nested-source-*.json'):
    if path.name.endswith('.limits.json') or path.name == 'nested-source-manifest.json':
        continue
    meta = json.loads(path.read_text())
    if 'command' in meta and 'source' in meta:
        assert sha(HERE / meta['source']) == meta['sha256'], path.name
        assert (HERE / meta['log']).exists(), path.name
for stem in ['nested-source-direct-1', 'nested-source-direct-3', 'nested-source-kernels-1', 'nested-source-kernels-2']:
    assert json.loads((HERE / (stem + '.json')).read_text())['exit_code'] == 1, stem
print(json.dumps(dict(status='PASS', entries=len(manifest['entries']), public_pairs=5,
                      constructed_pairs=2, full_proof=True, strict_empty=True,
                      memory_max_high_bytes=4294967296, swap_max_bytes=0)))
